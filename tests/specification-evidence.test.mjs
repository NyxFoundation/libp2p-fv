import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';
import { APALACHE_JAR_SHA256, APALACHE_LAUNCHER_SHA256,
  classifyTlc, classifyScenarios } from '../scripts/verification-results.mjs';

const root = new URL('../', import.meta.url);
const evidence = new URL('evidence/specification-safety/', root);
const read = path => readFileSync(new URL(path, evidence), 'utf8');
const report = JSON.parse(read('summary.json'));
const probes = new Map([
  ['cancellationGap', 'cancelViolation'], ['generationGap', 'staleViolation'],
  ['wireResetNotCancellation', 'resetSelectionViolation'], ['terminalHandoffGap', 'installationViolation'],
]);
const complete = ['sessionProtected', 'discardReset', 'deliverBufferedReset', 'eitherReset', 'handoffBoundary'];

test('should identify the tested inputs and finite evidence class when reading the audit report', () => {
  assert.equal(report.status, 'passed');
  assert.equal(report.evidenceClass, 'finite-state-model-checking');
  assert.equal(report.profile, 'specification-boundary-v1');
  assert.equal(report.tools.jarSha256, APALACHE_JAR_SHA256);
  assert.equal(report.tools.launcherSha256, APALACHE_LAUNCHER_SHA256);
  assert.deepEqual(report.assessedObligations, ['R-03.01', 'R-04.01', 'N-05.01', 'N-05.02']);
  for (const [path, digest] of Object.entries(report.source.sha256)) {
    assert.equal(createHash('sha256').update(readFileSync(new URL(path, root))).digest('hex'), digest,
      'Captured audit input changed: ' + path);
  }
});

test('should reproduce every recorded exploration and probe when reclassifying the logs', () => {
  assert.equal(report.results.length, 13);
  for (const name of [...complete, ...probes.keys()]) {
    const recorded = report.results.find(item => item.name === name);
    const monitor = probes.get(name);
    assert.equal(recorded?.expected, monitor ? 'counterexample' : 'complete');
    const actual = classifyTlc(read(name + '.log'), monitor ? 1 : 0, monitor);
    for (const [key, value] of Object.entries(actual)) assert.equal(recorded[key], value);
  }
  for (const [name, count] of [['scenarios', 17], ['unguarded_scenarios', 3]]) {
    const recorded = report.results.find(item => item.name === name);
    assert.equal(recorded.status, 'passed');
    assert.equal(recorded.tests, count);
    assert.deepEqual(classifyScenarios(read(name + '.log'), 0, count), { status: 'passed', tests: count });
  }
});

test('should not label design probes as specification defects when reporting counterexamples', () => {
  assert.equal(report.results.find(item => item.name === 'wireResetNotCancellation').role,
    'overstrong-hypothesis-counterexample');
  for (const name of ['cancellationGap', 'generationGap', 'terminalHandoffGap']) {
    assert.equal(report.results.find(item => item.name === name).role, 'local-contract-probe');
  }
  assert.equal(report.results.find(item => item.name === 'handoffBoundary').role, 'boundary-projection-check');
});
