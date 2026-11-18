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
  const result = spawnSync(process.execPath, ['scripts/verify-negotiation-safety.mjs'], {
    cwd: root, env: { ...process.env, ...env }, encoding: 'utf8',
  });
  assert.ifError(result.error);
  assert.equal(result.status, expectedExit, result.stdout + result.stderr);
  const directory = result.stdout.match(/^Evidence: (.+)$/m)?.[1];
  assert.ok(directory, 'The verifier must record an evidence directory');
  assert.equal(dirname(directory), join(root, '.artifacts/negotiation-safety'));
  if (expectedExit === 0) process.stdout.write(result.stdout);
  else t.after(() => rmSync(directory, { recursive: true, force: true }));
  return JSON.parse(readFileSync(join(directory, 'summary.json'), 'utf8'));
}

test('should record four completed explorations when the pinned model runs', t => {
  const report = runVerifier(t, {}, 0);
  assert.equal(report.status, 'passed');
  assert.equal(report.profile, 'abstract-negotiation-v1');
  assert.deepEqual(report.obligations, ['N-05.01', 'N-05.02']);
  assert.equal(report.results.find(item => item.name === 'scenarios')?.tests, 18);
  assert.deepEqual(report.results.filter(item => item.status === 'complete').map(item => item.name),
    ['singleStream', 'concurrentStreams', 'reconnectingPeer', 'independentPeers']);
});

test('should reject a changed tool file before running the cached launcher', t => {
  for (const damaged of ['jar', 'launcher']) {
    const cache = mkdtempSync(join(tmpdir(), 'libp2p-negotiation-preflight-'));
    t.after(() => rmSync(cache, { recursive: true, force: true }));
    const dist = join(cache, distribution);
    mkdirSync(join(dist, 'bin'), { recursive: true });
    mkdirSync(join(dist, 'lib'));
    const jar = join(dist, 'lib/apalache.jar');
    if (damaged === 'jar') writeFileSync(jar, 'changed');
    else symlinkSync(goodJar, jar);
    const marker = join(cache, 'launcher-ran');
    writeFileSync(join(dist, 'bin/apalache-mc'), "#!/bin/sh\ntouch '" + marker + "'\n", { mode: 0o755 });
    const report = runVerifier(t, { QUINT_HOME: cache }, 1);
    assert.equal(report.status, 'failed');
    assert.equal(report.error, 'Apalache distribution checksum mismatch');
    assert.deepEqual(report.results, []);
    assert.equal(existsSync(marker), false);
  }
});

test('should report failed verification when Java cannot report its version', t => {
  const bin = mkdtempSync(join(tmpdir(), 'libp2p-negotiation-java-'));
  t.after(() => rmSync(bin, { recursive: true, force: true }));
  writeFileSync(join(bin, 'java'), '#!/bin/sh\nexit 1\n', { mode: 0o755 });
  const report = runVerifier(t, { PATH: bin + ':' + process.env.PATH }, 1);
  assert.equal(report.status, 'failed');
  assert.equal(report.error, 'Java version check failed');
  assert.deepEqual(report.results, []);
});
