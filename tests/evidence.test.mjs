import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';
import { APALACHE_JAR_SHA256, APALACHE_LAUNCHER_SHA256,
  classifyTlc, classifyScenarios } from '../scripts/verification-results.mjs';

const root = new URL('../', import.meta.url);
const evidence = new URL('evidence/session-safety/', root);
const read = (base, path) => readFileSync(new URL(path, base), 'utf8');
const report = JSON.parse(read(evidence, 'summary.json'));

// The captured pre-commit run identifies actual inputs by digest, not just its base HEAD.
test('should match every captured verification input when reading published evidence', () => {
  assert.equal(report.status, 'passed');
  assert.equal(report.profile, 'abstract-session-v1');
  assert.equal(report.evidenceClass, 'finite-state-model-checking');
  assert.equal(report.tools.jarSha256, APALACHE_JAR_SHA256);
  assert.equal(report.tools.launcherSha256, APALACHE_LAUNCHER_SHA256);
  assert.deepEqual(report.obligations, ['R-03.01', 'R-04.01']);
  for (const [path, digest] of Object.entries(report.source.sha256)) {
    const actual = createHash('sha256').update(readFileSync(new URL(path, root))).digest('hex');
    assert.equal(actual, digest, `Captured input changed: ${path}; rerun npm run verify and refresh evidence`);
  }
});

test('should reproduce the recorded results when classifying published logs', () => {
  const safe = ['single', 'reconnect', 'peers', 'generations', 'concurrent'];
  const mutants = new Map([
    ['missingCancellationGuard', 'cancelViolation'],
    ['missingGenerationGuard', 'staleViolation'],
  ]);
  assert.equal(report.results.length, 10);
  for (const name of [...safe, ...mutants.keys()]) {
    const result = report.results.find(item => item.name === name);
    const monitor = mutants.get(name);
    assert.equal(result.expected, monitor ? 'counterexample' : 'complete');
    const actual = classifyTlc(read(evidence, `${name}.log`), monitor ? 1 : 0, monitor);
    for (const [key, value] of Object.entries(actual)) assert.equal(result[key], value);
  }
  assert.deepEqual(classifyScenarios(read(evidence, 'scenarios.log'), 0, 20), { status: 'passed', tests: 20 });
});
