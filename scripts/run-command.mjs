import { spawn } from 'node:child_process';
import { openSync, closeSync, readFileSync, statSync } from 'node:fs';

// Dedicated process groups ensure a timed-out verifier cannot leave Java children running.
export function runCommand(command, args, { cwd, log, env = {}, timeoutMs = 600_000, maxLogBytes = 16_777_216 }) {
  return new Promise((resolve, reject) => {
    const fd = openSync(log, 'w');
    const started = Date.now();
    const child = spawn(command, args, {
      cwd, detached: true, stdio: ['ignore', fd, fd],
      env: { ...process.env, ...env, NO_COLOR: '1' },
    });
    closeSync(fd);
    let interrupted = false;
    const stop = () => {
      interrupted = true;
      if (!Number.isInteger(child.pid) || child.pid <= 0) return;
      try { process.kill(-child.pid, 'SIGKILL'); }
      catch (error) { if (error.code !== 'ESRCH') throw error; }
    };
    const timer = setTimeout(stop, timeoutMs);
    process.once('SIGTERM', stop);
    process.once('SIGINT', stop);
    const cleanup = () => {
      clearTimeout(timer);
      process.removeListener('SIGTERM', stop);
      process.removeListener('SIGINT', stop);
    };
    child.once('error', () => {
      cleanup();
      reject(new Error('Verification command could not start'));
    });
    child.once('close', code => {
      cleanup();
      if (interrupted) return reject(new Error('Verification command was interrupted or timed out'));
      try {
        if (statSync(log).size > maxLogBytes) throw new Error('Verification log exceeds the read limit');
        resolve({ code, output: readFileSync(log, 'utf8'), durationMs: Date.now() - started });
      } catch {
        reject(new Error('Verification log is unavailable or exceeds the read limit'));
      }
    });
  });
}
