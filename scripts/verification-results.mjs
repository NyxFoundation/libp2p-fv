export const APALACHE_VERSION = '0.62.4';
export const APALACHE_JAR_SHA256 = 'e5223915507b65cc5f1638bd037ede60f8a4fc1644aff46355779f9b05df9262';
export const APALACHE_LAUNCHER_SHA256 = 'f8d4643705369d0642d9345a479e7cc8b7929710dc966e7f9a374bf03e526fe4';

// Retain warnings, tool identity, every trace state, and search statistics.
export function normalizeLog(output, root, home) {
  const text = output.replaceAll(root, '<REPO>').replaceAll(home, '<HOME>');
  const lines = text.split('\n').filter(line =>
    !/^(Parsing file |Semantic processing of module |Linting of module )/.test(line));
  return lines.join('\n');
}

export function classifyTlc(output, code, expectedMonitor) {
  if (!output.includes(`APALACHE version: ${APALACHE_VERSION} | build: 7954daf`)) {
    throw new Error('Pinned translator version was not observed in the log');
  }
  if (expectedMonitor) return classifyCounterexample(output, code, expectedMonitor);
  const counts = output.match(/(\d+) states generated, (\d+) distinct states found, 0 states left on queue\./);
  const depth = output.match(/The depth of the complete state graph search is (\d+)\./);
  if (code !== 0 || !counts || !depth || output.includes('Error:') ||
      !output.includes('Model checking completed. No error has been found.')) {
    throw new Error('TLC did not complete the finite exploration successfully');
  }
  return { status: 'complete', generated: Number(counts[1]), distinct: Number(counts[2]), depth: Number(depth[1]) };
}

function classifyCounterexample(output, code, monitor) {
  const states = [...output.matchAll(/State (\d+): </g)];
  if (code !== 1 || !states.length || !output.includes('Error: Invariant q_inv is violated.') ||
      !output.includes(`${monitor} |-> TRUE`) || !output.includes('error: found a counterexample')) {
    throw new Error('Mutation did not produce the intended invariant counterexample');
  }
  return { status: 'counterexample', traceStates: Number(states.at(-1)[1]) };
}

export function classifyScenarios(output, code, expectedTests) {
  const count = output.match(/\b(\d+) passing \(/);
  if (code !== 0 || Number(count?.[1]) !== expectedTests) {
    throw new Error('The expected scenario suite did not pass completely');
  }
  return { status: 'passed', tests: expectedTests };
}
