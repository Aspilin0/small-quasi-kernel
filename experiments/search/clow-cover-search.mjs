import assert from 'node:assert/strict';
import { allCores, attachments, indices, orbitFilter } from '../shared/clow-cores.mjs';
import { checkRealizations, minima } from '../shared/clow-minima.mjs';
import { eachDoubleCover } from '../shared/clow-switches.mjs';


// r=0, x=1, a=2, b=3, s=4. The two paths x-a-s and x-b-s
// must merge for r to tie, and separate for x to tie.
const conflict = [[1,5,6],[2,3],[4,7],[4,8],[0,9],[10,11],[12,13],[],[],[],[1],[],[1],[]];
const local = checkRealizations(conflict);
assert.deepEqual(local.slice(0,2), [0,0]);
console.log('Two roots, local minima:', local.slice(0,2));
const pairCases = { onlyR: 0, onlyX: 0, both: 0, neither: 0 };
const observed = conflict.map(() => Infinity);
eachDoubleCover(conflict, rows => {
  const r = rows[0].gap > 0, x = rows[2].gap > 0;
  const key = r ? (x ? 'both' : 'onlyR') : (x ? 'onlyX' : 'neither');
  ++pairCases[key];
  for (let i=0; i<conflict.length; ++i) observed[i] = Math.min(observed[i], rows[2*i].gap);
});
assert.equal(pairCases.neither, 0);
assert.ok(pairCases.onlyR > 0 && pairCases.onlyX > 0);
assert.deepEqual(observed, local);
console.log('Two roots, joint switch classes:', pairCases);


function scan(n) {
  const take = n === 6 ? orbitFilter(n) : () => true;
  let cores = 0, graphs = 0, passing = 0, fewest = Infinity, example;
  allCores(n, core => {
    if (!take(core)) return;
    ++cores;
    attachments(core, (rows, order) => {
      ++graphs;
      const best = minima(rows, order);
      const fixed = best.filter(r => r.gap > 0).length;
      if (!fixed) ++passing;
      if (fixed < fewest) {
        fewest = fixed;
        example = Array.from({length:order}, (_,i) => indices(rows[i] ?? 0));
        assert.deepEqual(checkRealizations(example), best.map(r => r.gap));
      }
    });
  });
  return { n, cores, graphs, passing, fewest, example };
}
for (const n of (process.argv.includes('--six') ? [3,4,5,6] : [3,4,5])) {
  console.log(JSON.stringify(scan(n)));
}
