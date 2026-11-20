import assert from 'node:assert/strict';
import { after, test } from 'node:test';
import { classifyTlc, classifyScenarios, normalizeLog } from '../scripts/verification-results.mjs';
import { runCommand } from '../scripts/run-command.mjs';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const logs = mkdtempSync(join(tmpdir(), 'libp2p-verifier-test-'));
after(() => rmSync(logs, { recursive: true, force: true }));

const completed = `APALACHE version: 0.62.4 | build: 7954daf
Model checking completed. No error has been found.
2107 states generated, 91 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 8.
[ok] No violation found`;
const violation = `APALACHE version: 0.62.4 | build: 7954daf
Error: Invariant q_inv is violated.
State 1: <Initial predicate>
State 7: <use>
cancelViolation |-> TRUE
[violation] Found an issue
error: found a counterexample`;

test('should preserve evidence and warnings when normalizing verbose tool logs', () => {
  const input = ['Parsing file /home/test/repo/model.tla', 'Semantic processing of module X',
    'Linting of module X', 'WARNING: tool warning', '/home/test/repo /home/test', violation].join('\n');
  const log = normalizeLog(input, '/home/test/repo', '/home/test');
  assert.equal(log, ['WARNING: tool warning', '<REPO> <HOME>', violation].join('\n'));
  assert.deepEqual(classifyTlc(log, 1, 'cancelViolation'), { status: 'counterexample', traceStates: 7 });
});

test('should accept complete finite exploration when the queue is empty', () => {
  assert.deepEqual(classifyTlc(completed, 0), {
    status: 'complete', generated: 2107, distinct: 91, depth: 8,
  });
});

test('should reject exploration when a successful exit lacks completion evidence', () => {
  for (const output of ['', '[ok] No violation found', `${completed}\nError: incomplete`,
    completed.replace('0 states left', '1 states left')]) {
    assert.throws(() => classifyTlc(output, 0));
  }
});

test('should reject exploration when the process fails or times out', () => {
  for (const code of [1, null]) assert.throws(() => classifyTlc(completed, code));
});

test('should accept mutation only when the intended monitor has a counterexample', () => {
  assert.deepEqual(classifyTlc(violation, 1, 'cancelViolation'), {
    status: 'counterexample', traceStates: 7,
  });
});

test('should reject mutation when an unrelated failure replaces the counterexample', () => {
  for (const output of ['Java error', violation.replace('cancelViolation |-> TRUE', 'staleViolation |-> TRUE')]) {
    assert.throws(() => classifyTlc(output, 1, 'cancelViolation'));
  }
  assert.throws(() => classifyTlc(violation, null, 'cancelViolation'));
  assert.throws(() => classifyTlc(completed, 0, 'cancelViolation'));
  assert.throws(() => classifyTlc(violation, 1));
});

test('should reject evidence when it came from an unpinned translator', () => {
  assert.throws(() => classifyTlc(completed.replace('0.62.4', '0.62.1'), 0));
  assert.throws(() => classifyTlc(violation.replace('0.62.4', '0.62.1'), 1, 'cancelViolation'));
});

test('should capture output and nonzero exit when a tool fails', async () => {
  const result = await runCommand(process.execPath,
    ['-e', 'process.stdout.write("expected failure"); process.exitCode = 7'],
    { log: join(logs, 'failed.log') });
  assert.equal(result.code, 7);
  assert.equal(result.output, 'expected failure');
  assert.ok(result.durationMs >= 0);
});

test('should reject when a verification tool cannot start', async () => {
  await assert.rejects(runCommand('/nonexistent-libp2p-test-tool', [],
    { log: join(logs, 'missing.log') }), /could not start/);
});

test('should reject before spawning when the log directory does not exist', async () => {
  await assert.rejects(runCommand(process.execPath, ['-e', 'process.exitCode = 0'],
    { log: join(logs, 'absent', 'missing.log') }), { code: 'ENOENT' });
});

test('should reject oversized output before reading a tool log into memory', async () => {
  await assert.rejects(runCommand(process.execPath, ['-e', 'process.stdout.write("x".repeat(64))'],
    { log: join(logs, 'large.log'), maxLogBytes: 32 }), /read limit/);
});

test('should terminate when a verification command exceeds its deadline', async () => {
  await assert.rejects(runCommand(process.execPath, ['-e', 'setInterval(() => {}, 1000)'],
    { log: join(logs, 'timeout.log'), timeoutMs: 50 }), /timed out/);
});

test('should accept scenarios only when all expected cases pass', () => {
  assert.deepEqual(classifyScenarios('15 passing (58ms)', 0, 15), { status: 'passed', tests: 15 });
  assert.throws(() => classifyScenarios('14 passing (58ms)', 0, 15));
  assert.throws(() => classifyScenarios('15 passing (58ms)', 1, 15));
  assert.throws(() => classifyScenarios('no tests', 0, 15));
});
