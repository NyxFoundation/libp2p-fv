import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { createServer } from 'node:net';
import { homedir } from 'node:os';
import { dirname, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand } from './run-command.mjs';
import { APALACHE_VERSION, APALACHE_JAR_SHA256, APALACHE_LAUNCHER_SHA256,
  classifyTlc, classifyScenarios, normalizeLog } from './verification-results.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const model = 'models/session-safety/instances.qnt';
const scenarios = 'models/session-safety/scenarios.qnt';
const cli = join(root, 'node_modules/@informalsystems/quint/dist/src/cli.js');
const output = join(root, '.artifacts/session-safety', new Date().toISOString().replaceAll(':', '-'));
const matrix = ['single', 'reconnect', 'peers', 'generations', 'concurrent'];
const mutants = [
  ['missingCancellationGuard', 'cancellationSafe', 'cancelViolation'],
  ['missingGenerationGuard', 'generationSafe', 'staleViolation'],
];
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const git = (...args) => execFileSync('git', args, { cwd: root, encoding: 'utf8' }).trim();
const save = report => writeFileSync(join(output, 'summary.json'), `${JSON.stringify(report, null, 2)}\n`);

function sourceHashes() {
  const directories = ['models/session-safety', 'scripts', 'tests', '.github/workflows'];
  const files = ['package.json', 'package-lock.json', 'docs/session-safety.md', ...directories.flatMap(directory =>
    readdirSync(join(root, directory), { recursive: true, withFileTypes: true })
      .filter(entry => entry.isFile())
      .map(entry => relative(root, join(entry.parentPath, entry.name))))];
  return Object.fromEntries(files.sort().map(file => [file, sha256(readFileSync(join(root, file)))]));
}

async function unusedPort() {
  const server = createServer();
  await new Promise((resolvePort, reject) => {
    server.once('error', reject);
    server.listen(0, '127.0.0.1', resolvePort);
  });
  const { port } = server.address();
  await new Promise((resolveClose, reject) => server.close(error => error ? reject(error) : resolveClose()));
  return port;
}

function checkJar() {
  const home = process.env.QUINT_HOME ?? join(homedir(), '.quint');
  const distribution = join(home, `apalache-dist-${APALACHE_VERSION}/apalache`);
  const jar = sha256(readFileSync(join(distribution, 'lib/apalache.jar')));
  const launcher = sha256(readFileSync(join(distribution, 'bin/apalache-mc')));
  if (jar !== APALACHE_JAR_SHA256 || launcher !== APALACHE_LAUNCHER_SHA256) {
    throw new Error('Apalache/TLC distribution checksum mismatch');
  }
  return join(distribution, 'lib/apalache.jar');
}

async function execute(name, args, classify) {
  process.stdout.write(`Checking ${name}...\n`);
  const log = join(output, `${name}.log`);
  const env = { APALACHE_JAR: checkJar(), JVM_ARGS: '-Xmx1G', JVM_GC_ARGS: '-XX:+UseG1GC' };
  const result = await runCommand(process.execPath, [cli, ...args], { cwd: root, log, env });
  // Keep useful counterexamples without publishing machine-specific home paths.
  writeFileSync(log, normalizeLog(result.output, root, homedir()));
  return { name, command: ['quint', ...args], durationMs: result.durationMs, ...classify(result) };
}

async function verifyInstance(name, invariant, monitor) {
  // A fresh endpoint prevents silently reusing a different translator already on port 8822.
  const port = await unusedPort();
  const args = ['verify', model, `--main=${name}`, '--backend=tlc',
    `--apalache-version=${APALACHE_VERSION}`, `--server-endpoint=localhost:${port}`,
    `--invariant=${invariant}`, '--tlc-config=models/session-safety/tlc.json', '--verbosity=3'];
  checkJar();
  const result = await execute(name, args, ({ output: text, code }) => classifyTlc(text, code, monitor));
  checkJar();
  return { ...result, expected: monitor ? 'counterexample' : 'complete' };
}

async function verify(report) {
  const quint = JSON.parse(readFileSync(join(root, 'node_modules/@informalsystems/quint/package.json')));
  if (quint.version !== '0.33.1') throw new Error('Run npm ci to install the pinned Quint version');
  report.tools = {
    node: process.version,
    quint: quint.version, apalache: APALACHE_VERSION, jarSha256: APALACHE_JAR_SHA256,
    launcherSha256: APALACHE_LAUNCHER_SHA256, translatorJvmArgs: '-Xmx1G -XX:+UseG1GC',
  };
  const prepared = await runCommand(process.execPath, ['scripts/prepare-apalache.mjs'],
    { cwd: root, log: join(output, 'prepare-distribution.log') });
  if (prepared.code !== 0) throw new Error('Apalache distribution preparation failed');
  checkJar();
  // Java writes its version to stderr, so capture it separately in the artifact directory.
  const java = await runCommand('java', ['-version'], { cwd: root, log: join(output, 'java.log') });
  if (java.code !== 0) throw new Error('Java version check failed');
  report.tools.java = java.output.trim();
  for (const input of [model, scenarios]) {
    const name = input === model ? 'typecheck-instances' : 'typecheck-scenarios';
    report.results.push(await execute(name, ['typecheck', input], ({ code }) => {
      if (code !== 0) throw new Error('Quint type checking failed');
      return { status: 'passed' };
    }));
  }
  report.results.push(await execute('scenarios', ['test', scenarios, '--backend=typescript',
    '--seed=1', '--max-samples=1'], ({ output: text, code }) => classifyScenarios(text, code, 20)));
  for (const name of matrix) {
    report.results.push(await verifyInstance(name, 'safety'));
    save(report);
  }
  for (const [name, invariant, monitor] of mutants) {
    report.results.push(await verifyInstance(name, invariant, monitor));
    save(report);
  }
}

async function main() {
  if (process.platform !== 'linux') throw new Error('This verifier requires Linux process groups');
  if (process.argv.length !== 2) throw new Error('This verifier takes no command-line arguments');
  mkdirSync(output, { recursive: true });
  const report = {
    status: 'running', startedAt: new Date().toISOString(),
    evidenceClass: 'finite-state-model-checking',
    profile: 'abstract-session-v1',
    specificationSnapshot: 'libp2p/specs@c750236de43cd8b246a824b377dfdb26bae686db',
    obligations: ['R-03.01', 'R-04.01'],
    source: { head: git('rev-parse', 'HEAD'), branch: git('branch', '--show-current'),
      dirty: git('status', '--porcelain').length > 0, sha256: sourceHashes() },
    results: [],
  };
  save(report);
  try {
    await verify(report);
    if (JSON.stringify(sourceHashes()) !== JSON.stringify(report.source.sha256)) {
      throw new Error('Verification inputs changed while the checks were running');
    }
    report.status = 'passed';
  } catch (error) {
    report.status = 'failed';
    report.error = error.message;
    throw error;
  } finally {
    report.finishedAt = new Date().toISOString();
    save(report);
    process.stdout.write(`Evidence: ${output}\n`);
  }
}

main().catch(() => {
  process.stderr.write('Session-safety verification failed; inspect the evidence logs.\n');
  process.exitCode = 1;
});
