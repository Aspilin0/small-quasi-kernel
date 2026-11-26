import assert from 'node:assert/strict';
import { inspect } from './clow-check.mjs';

// 0=a, 1=b, 2,3,4=t_i, 5=z. The directed cycle starts at vertex 6.
function build(m) {
  const out = [[1,5], [2,3,4], [0], [0], [0], []];
  for (let i = 0; i < m; ++i) out.push([0,1,6+(i+1)%m]);
  return out;
}

const arg = process.argv[2];
if (arg !== undefined) {
  const m = Number(arg);
  assert.ok(Number.isSafeInteger(m) && m >= 3, 'cycle length must be an integer >= 3');
  console.log(JSON.stringify(build(m)));
} else {
  for (let m = 3; m <= 40; ++m) {
    const rows = inspect(build(m));
    assert.deepEqual(rows.map(r => r.gap), [0,3,0,0,0,0,...Array(m).fill(-1)]);
  }
  console.log('Cycle family checked at all 38 lengths from 3 through 40.');
}
