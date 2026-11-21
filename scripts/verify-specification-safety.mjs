import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { createReadStream, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand } from './run-command.mjs';
import {
  APALACHE_VERSION, APALACHE_JAR_SHA256, APALACHE_LAUNCHER_SHA256,
  classifyScenarios, classifyTlc, normalizeLog,
} from './verification-results.mjs';

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const model = 'models/specification-safety/instances.qnt';
const scenarios = 'models/specification-safety/scenarios.qnt';
const config = 'models/session-safety/tlc.json';
const quint = 'node_modules/@informalsystems/quint';
const matrix = [
  ['sessionProtected', 'sessionProtected', 'safety', null, 'conditional-design-check'],
  ['cancellationGap', 'cancellationGap', 'cancellationSafe', 'cancelViolation', 'local-contract-probe'],
  ['generationGap', 'generationGap', 'generationSafe', 'staleViolation', 'local-contract-probe'],
  ['discardReset', 'discardReset', 'discardSafety', null, 'conditional-design-check'],
  ['deliverBufferedReset', 'deliverBufferedReset', 'safety', null, 'conditional-design-check'],
  ['eitherReset', 'eitherReset', 'safety', null, 'conditional-design-check'],
  ['handoffBoundary', 'unguardedHandoff', 'boundarySafety', null, 'boundary-projection-check'],
  ['wireResetNotCancellation', 'eitherReset', 'wireResetStopsSelection', 'resetSelectionViolation',
    'overstrong-hypothesis-counterexample'],
  ['terminalHandoffGap', 'unguardedHandoff', 'installationSafe', 'installationViolation', 'local-contract-probe'],
];
const inputs = [
  model, scenarios, config, 'models/specification-safety/reset-boundary.qnt',
  'models/session-safety/lifecycle.qnt', 'package.json', 'package-lock.json',
  'scripts/verify-specification-safety.mjs', 'scripts/run-command.mjs',
  'scripts/verification-results.mjs', 'scripts/prepare-apalache.mjs',
  '.github/workflows/specification-safety.yml', 'tests/specification-audit-runner.mjs',
  'tests/specification-evidence.test.mjs', 'docs/specification-safety-audit.md',
];
const read = path => readFileSync(join(root, path));
const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
const sourceHashes = () => Object.fromEntries(inputs.map(path =>
  [path, createHash('sha256').update(read(path)).digest('hex')]));

async function digest(path) {
  const hash = createHash('sha256');
  for await (const chunk of createReadStream(path)) hash.update(chunk);
  return hash.digest('hex');
}

async function checkedJar(home) {
  const dist = join(home, 'apalache-dist-' + APALACHE_VERSION, 'apalache');
  const jar = join(dist, 'lib/apalache.jar');
  if (await digest(jar) !== APALACHE_JAR_SHA256 ||
      await digest(join(dist, 'bin/apalache-mc')) !== APALACHE_LAUNCHER_SHA256) {
    throw new Error('Apalache distribution checksum mismatch');
  }
  return jar;
}

async function execute(output, env, name, args, classify) {
  process.stdout.write('Checking ' + name + '...\n');
  const log = join(output, name + '.log');
  const result = await runCommand(process.execPath, [join(root, quint, 'dist/src/cli.js'), ...args],
    { cwd: root, log, env });
  writeFileSync(log, normalizeLog(result.output, root, homedir()));
  return { name, command: ['quint', ...args], durationMs: result.durationMs, ...classify(result) };
}

function checkExit({ code }, stage) {
  if (code !== 0) throw new Error(stage + ' failed');
  return { status: 'passed' };
}

async function verify(output, report) {
  const version = JSON.parse(read(quint + '/package.json')).version;
  if (version !== '0.33.1') throw new Error('Install the pinned Quint version');
  const home = resolve(process.env.QUINT_HOME ?? join(homedir(), '.quint'));
  const jar = await checkedJar(home);
  const env = { QUINT_HOME: home, APALACHE_JAR: jar, JVM_ARGS: '-Xmx1G', JVM_GC_ARGS: '-XX:+UseG1GC' };
  const java = await runCommand('java', ['-version'], { cwd: root, log: join(output, 'java.log') });
  checkExit(java, 'Java version check');
  report.tools = { node: process.version, quint: version, java: java.output.trim(),
    apalache: APALACHE_VERSION, jarSha256: APALACHE_JAR_SHA256,
    launcherSha256: APALACHE_LAUNCHER_SHA256, translatorJvmArgs: '-Xmx1G -XX:+UseG1GC' };
  for (const [name, input] of [['instances', model], ['scenarios', scenarios]]) {
    report.results.push(await execute(output, env, 'typecheck-' + name, ['typecheck', input],
      result => checkExit(result, 'Quint type check')));
  }
  for (const [name, count] of [['scenarios', 17], ['unguarded_scenarios', 3]]) {
    report.results.push(await execute(output, env, name, ['test', scenarios, '--main=' + name,
      '--backend=typescript', '--seed=1', '--max-samples=1'],
    ({ output: text, code }) => classifyScenarios(text, code, count)));
  }
  for (const [name, main, invariant, monitor, role] of matrix) {
    await checkedJar(home);
    const result = await execute(output, env, name, [
      'verify', model, '--main=' + main, '--backend=tlc', '--apalache-version=' + APALACHE_VERSION,
      '--invariant=' + invariant, '--tlc-config=' + config, '--verbosity=3',
    ], ({ output: text, code }) => classifyTlc(text, code, monitor));
    report.results.push({ ...result, expected: monitor ? 'counterexample' : 'complete', role });
  }
  await checkedJar(home);
}

function loopbackOnly() {
  if (process.platform !== 'linux') return false;
  try {
    const links = readFileSync('/proc/net/dev', 'utf8').trimEnd().split('\n').slice(2);
    return links.map(link => link.split(':', 1)[0].trim()).join('\n') === 'lo';
  } catch {
    return false;
  }
}

async function main() {
  if (!loopbackOnly()) {
    process.stderr.write('Run the verifier in a Linux network namespace with loopback only.\n');
    process.exitCode = 1;
    return;
  }
  const base = join(root, '.artifacts/specification-safety');
  mkdirSync(base, { recursive: true });
  const output = mkdtempSync(join(base, new Date().toISOString().replaceAll(':', '-') + '-'));
  const report = {
    status: 'failed', startedAt: new Date().toISOString(), profile: 'specification-boundary-v1',
    evidenceClass: 'finite-state-model-checking',
    interpretation: 'Contrast checks supporting a manual source audit; not a full specification conformance proof.',
    assessedObligations: ['R-03.01', 'R-04.01', 'N-05.01', 'N-05.02'],
    specificationSnapshots: { libp2pSpecs: 'c750236de43cd8b246a824b377dfdb26bae686db',
      multistreamSelect: '9a1fbe8edadebea223f47102f1913b8026c23a1c', quic: 'RFC 9000, sections 2.4, 3.2, 3.3' },
    source: { head: git('rev-parse', 'HEAD'), dirty: git('status', '--porcelain').length > 0,
      sha256: sourceHashes() }, results: [],
  };
  try {
    await verify(output, report);
    if (JSON.stringify(sourceHashes()) !== JSON.stringify(report.source.sha256)) {
      throw new Error('Verification inputs changed during the run');
    }
    report.status = 'passed';
  } catch (error) {
    report.error = normalizeLog(error.message, root, homedir());
    throw error;
  } finally {
    report.finishedAt = new Date().toISOString();
    writeFileSync(join(output, 'summary.json'), JSON.stringify(report, null, 2) + '\n');
    process.stdout.write('Evidence: ' + output + '\n');
  }
}

main().catch(() => {
  process.stderr.write('Specification-safety audit failed; inspect the evidence logs.\n');
  process.exitCode = 1;
});
