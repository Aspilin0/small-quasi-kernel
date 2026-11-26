import assert from 'node:assert/strict';
import { inspect } from './clow-check.mjs';

import { allCores, attachments, bit, indices, size } from './clow-cores.mjs';

function search(generate) {
  let cores = 0, graphs = 0, minimum = Infinity, best;
  generate(core => {
    ++cores;
    attachments(core, (rows, n) => {
      ++graphs;
      let good = 0;
      for (let v = 0; v < core.length; ++v) {
        const removed = rows[v] | bit(v);
        let hit = 0;
        for (let u = 0; u < core.length; ++u)
          if (!(removed & bit(u))) hit |= rows[u];
        const sources = (bit(n)-1) & ~(removed | hit);
        let expansion = rows[v];
        for (let u = 0; u < core.length; ++u)
          if (sources & bit(u)) expansion |= rows[u];
        if (size(expansion) > size(sources)) ++good;
      }
      // Sinks in a sourceless graph always have empty S and E.
      if (good < minimum) {
        best = Array.from({length:n}, (_,v) => indices(rows[v] ?? 0));
        assert.equal(inspect(best).filter(row => row.gap > 0).length, good);
        minimum = good;
      }
    });
  });
  return { cores, graphs, minimum, best };
}

const reference = [[4,5],[3,7],[0,6],[2,4],[2,7],[1,6],[0,1],[3,5]];
const degreeFour = reference.map((row,i) => [...row,8+2*i,9+2*i]).concat(Array.from({length:16}, () => []));
assert.ok(inspect(degreeFour, 4).every(row => row.gap === 0));
const fixed = search(visit => visit(reference.map(row => row.reduce((m,v) => m | bit(v), 0))));
assert.equal(fixed.graphs, 21147);
console.log('Published core:', JSON.stringify(fixed));
for (const n of [3,4,5]) {
  console.log('Core order', n, JSON.stringify(search(visit => allCores(n, visit))));
}
