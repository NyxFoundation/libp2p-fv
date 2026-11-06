import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const read = path => readFileSync(path, 'utf8');

function publish() {
  if (process.argv.length !== 3) throw new Error('Supply one verifier evidence directory');
  const source = realpathSync(resolve(root, process.argv[2]));
  if (!source.startsWith(join(root, '.artifacts/session-safety') + sep)) {
    throw new Error('Evidence must come from the local verifier artifact directory');
  }
  const summary = read(join(source, 'summary.json'));
  const report = JSON.parse(summary);
  if (report.status !== 'passed' || report.profile !== 'abstract-session-v1') {
    throw new Error('Only a passed session-safety report may be published');
  }
  for (const [path, expected] of Object.entries(report.source.sha256)) {
    const file = realpathSync(resolve(root, path));
    if (!file.startsWith(root + sep)) throw new Error('Invalid input path in evidence');
    const digest = createHash('sha256').update(readFileSync(file)).digest('hex');
    if (digest !== expected) throw new Error('Inputs changed; rerun verification before publication');
  }
  const names = ['single', 'reconnect', 'peers', 'generations', 'concurrent',
    'missingCancellationGuard', 'missingGenerationGuard'];
  const entries = names.map(name => {
    const text = read(join(source, `${name}.log`));
    const start = text.indexOf('[TLC] Running TLC model checker...');
    const identity = text.match(/^# APALACHE version:.*$/m)?.[0];
    if (start < 0 || !identity) throw new Error('Incomplete TLC log');
    return [`${name}.log`, `${identity}\n${text.slice(start)}`];
  });
  const first = read(join(source, 'single.log'));
  entries.push(['translator.log', first.slice(0, first.indexOf('[TLC] Running TLC model checker...'))]);
  for (const name of ['java', 'scenarios', 'typecheck-instances', 'typecheck-scenarios']) {
    entries.push([`${name}.log`, read(join(source, `${name}.log`))]);
  }
  entries.push(['summary.json', summary]);
  const destination = join(root, 'evidence/session-safety');
  mkdirSync(destination, { recursive: true });
  for (const [name, content] of entries) writeFileSync(join(destination, name), content);
  process.stdout.write('Published session-safety evidence.\n');
}

try { publish(); }
catch {
  process.stderr.write('Evidence publication failed; check the artifact directory and input hashes.\n');
  process.exitCode = 1;
}
