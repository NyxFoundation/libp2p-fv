import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { test } from 'node:test';

test('should reject a corrupted cached distribution before executing its launcher', t => {
  const cache = mkdtempSync(join(tmpdir(), 'libp2p-corrupt-tool-'));
  t.after(() => rmSync(cache, { recursive: true, force: true }));
  const distribution = join(cache, 'apalache-dist-0.62.4/apalache');
  mkdirSync(join(distribution, 'bin'), { recursive: true });
  mkdirSync(join(distribution, 'lib'), { recursive: true });
  const marker = join(cache, 'launcher-was-executed');
  writeFileSync(join(distribution, 'lib/apalache.jar'), 'not the pinned JAR');
  writeFileSync(join(distribution, 'bin/apalache-mc'), `#!/bin/sh\ntouch '${marker}'\n`, { mode: 0o755 });
  const root = fileURLToPath(new URL('../', import.meta.url));
  const result = spawnSync(process.execPath, ['scripts/verify-session-safety.mjs'], {
    cwd: root, env: { ...process.env, QUINT_HOME: cache }, encoding: 'utf8', timeout: 20_000,
  });
  assert.equal(result.status, 1);
  assert.equal(existsSync(marker), false);
  const directory = result.stdout.match(/Evidence: (.+)\n/)?.[1];
  assert.ok(directory, 'A failed preflight must still record its evidence');
  const summary = JSON.parse(readFileSync(join(directory, 'summary.json'), 'utf8'));
  assert.equal(summary.status, 'failed');
  assert.equal(summary.error, 'Apalache/TLC distribution checksum mismatch');
  assert.deepEqual(summary.results, []);
});

test('should reject publication when an input symlink escapes the repository', t => {
  const directory = mkdtempSync(join(tmpdir(), 'libp2p-publication-test-'));
  t.after(() => rmSync(directory, { recursive: true, force: true }));
  const repo = join(directory, 'repo');
  const source = join(repo, '.artifacts/session-safety/run');
  mkdirSync(source, { recursive: true });
  mkdirSync(join(repo, 'scripts'));
  const script = readFileSync(new URL('../scripts/publish-session-evidence.mjs', import.meta.url));
  writeFileSync(join(repo, 'scripts/publish-session-evidence.mjs'), script);
  writeFileSync(join(directory, 'outside'), 'external content');
  symlinkSync(join(directory, 'outside'), join(repo, 'input'));
  const digest = createHash('sha256').update('external content').digest('hex');
  writeFileSync(join(source, 'summary.json'), JSON.stringify({
    status: 'passed', profile: 'abstract-session-v1', source: { sha256: { input: digest } },
  }));
  const log = '# APALACHE version: 0.62.4 | build: 7954daf\n[TLC] Running TLC model checker...\n';
  for (const name of ['single', 'reconnect', 'peers', 'generations', 'concurrent',
    'missingCancellationGuard', 'missingGenerationGuard', 'java', 'scenarios',
    'typecheck-instances', 'typecheck-scenarios']) writeFileSync(join(source, `${name}.log`), log);
  const result = spawnSync(process.execPath,
    ['scripts/publish-session-evidence.mjs', source], { cwd: repo, encoding: 'utf8', timeout: 5000 });
  assert.equal(result.status, 1);
  assert.equal(existsSync(join(repo, 'evidence')), false);
});
