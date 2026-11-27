import { execFileSync } from 'node:child_process';

const maxBytes = 20_000;
const exempt = /(^|\/)(node_modules|dist|build|coverage|\.lake|generated)\/|(^|\/)[^/]*lock\.(json|ya?ml)$|(^|\/)(yarn\.lock|bun\.lockb?|Cargo\.lock)$|\.(olean|ilean|log)$/;

// Read staged blob sizes so unstaged changes and checkout line endings do not affect the check.
const fields = execFileSync('git', [
  'diff', '--cached', '--raw', '--no-abbrev', '--no-renames', '--diff-filter=AMT', '-z',
], { encoding: 'utf8' }).split('\0');

for (let i = 0; i + 1 < fields.length; i += 2) {
  const [, mode, , objectId] = fields[i].split(' ');
  const path = fields[i + 1];
  if (!mode.startsWith('100') || exempt.test(path)) continue;

  const bytes = Number(execFileSync('git', ['cat-file', '-s', objectId], { encoding: 'utf8' }));
  if (bytes > maxBytes) {
    console.error(`${path} is ${bytes} bytes. Split it by topic or function before committing (limit ${maxBytes} bytes).`);
    process.exitCode = 1;
  }
}
