import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { homedir, tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { before, test } from 'node:test';
import { fileURLToPath } from 'node:url';
import { APALACHE_VERSION } from '../scripts/verification-results.mjs';

const root = fileURLToPath(new URL('../', import.meta.url));
const distribution = 'apalache-dist-' + APALACHE_VERSION + '/apalache';
const goodJar = resolve(process.env.QUINT_HOME ?? join(homedir(), '.quint'), distribution, 'lib/apalache.jar');
before(() => assert.ok(existsSync(goodJar), 'Run node scripts/prepare-apalache.mjs before testing the verifier'));

function runVerifier(t, env, expectedExit) {
  const result = spawnSync(process.execPath, ['scripts/verify-specification-safety.mjs'], {
    cwd: root, env: { ...process.env, ...env }, encoding: 'utf8', timeout: 600_000,
  });
  assert.ifError(result.error);
  assert.equal(result.status, expectedExit, result.stdout + result.stderr);
  const directory = result.stdout.match(/^Evidence: (.+)$/m)?.[1];
  assert.ok(directory, 'The verifier must record an evidence directory');
  assert.equal(dirname(directory), join(root, '.artifacts/specification-safety'));
  if (expectedExit === 0) process.stdout.write(result.stdout);
  else t.after(() => rmSync(directory, { recursive: true, force: true }));
  return JSON.parse(readFileSync(join(directory, 'summary.json'), 'utf8'));
}

function temporary(t, prefix) {
  const directory = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  return directory;
}

test('should distinguish completed checks from gap probes when the audit runs', t => {
  const report = runVerifier(t, {}, 0);
  assert.equal(report.status, 'passed');
  assert.equal(report.profile, 'specification-boundary-v1');
  assert.deepEqual(report.assessedObligations, ['R-03.01', 'R-04.01', 'N-05.01', 'N-05.02']);
  assert.equal(report.results.filter(item => item.status === 'complete').length, 5);
  assert.equal(report.results.filter(item => item.status === 'counterexample').length, 4);
  assert.equal(report.results.find(item => item.name === 'scenarios')?.tests, 17);
  assert.equal(report.results.find(item => item.name === 'unguarded_scenarios')?.tests, 3);
  assert.equal(report.results.find(item => item.name === 'wireResetNotCancellation')?.role,
    'overstrong-hypothesis-counterexample');
  assert.equal(report.results.filter(item => item.role === 'local-contract-probe').length, 3);
});

test('should reject a changed distribution before executing its launcher', t => {
  for (const damaged of ['jar', 'launcher']) {
    const cache = temporary(t, 'libp2p-audit-preflight-');
    const dist = join(cache, distribution);
    mkdirSync(join(dist, 'bin'), { recursive: true });
    mkdirSync(join(dist, 'lib'));
    if (damaged === 'jar') writeFileSync(join(dist, 'lib/apalache.jar'), 'changed');
    else symlinkSync(goodJar, join(dist, 'lib/apalache.jar'));
    const marker = join(cache, 'launcher-ran');
    writeFileSync(join(dist, 'bin/apalache-mc'), "#!/bin/sh\ntouch '" + marker + "'\n", { mode: 0o755 });
    const report = runVerifier(t, { QUINT_HOME: cache }, 1);
    assert.equal(report.status, 'failed');
    assert.equal(report.error, 'Apalache distribution checksum mismatch');
    assert.deepEqual(report.results, []);
    assert.equal(existsSync(marker), false);
  }
});

test('should fail without downloading when the prepared cache is missing', t => {
  const report = runVerifier(t, { QUINT_HOME: temporary(t, 'libp2p-audit-missing-') }, 1);
  assert.equal(report.status, 'failed');
  assert.deepEqual(report.results, []);
});

test('should fail when Java cannot report its version', t => {
  const bin = temporary(t, 'libp2p-audit-java-');
  writeFileSync(join(bin, 'java'), '#!/bin/sh\nexit 1\n', { mode: 0o755 });
  const report = runVerifier(t, { PATH: bin + ':' + process.env.PATH }, 1);
  assert.equal(report.status, 'failed');
  assert.equal(report.error, 'Java version check failed');
  assert.deepEqual(report.results, []);
});
