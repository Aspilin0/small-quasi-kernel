import assert from 'node:assert/strict';
import { bit, size } from './clow-cores.mjs';
import { inspect } from './clow-check.mjs';

// Inputs are row masks, including empty sink rows. This enumerator is used
// only for graphs with at most 30 vertices.
export function rootMinimum(rows, root, sources, mandatory) {
  let best = Infinity, keep = 0;
  const free = sources & ~mandatory;
  for (let subset = free;; subset = (subset - 1) & free) {
    const retained = mandatory | subset;
    let targets = rows[root];
    for (let s = retained; s; s &= s-1) targets |= rows[31-Math.clz32(s & -s)];
    const gap = size(targets) - size(retained);
    if (gap < best) { best = gap; keep = retained; }
    if (!subset) return { gap: best, keep };
  }
}

export function minima(coreRows, n) {
  assert.ok(n <= 30);
  const rows = Array.from({length:n}, (_,v) => coreRows[v] ?? 0);
  let seen = 0, multiple = 0;
  for (const row of rows) { multiple |= seen & row; seen |= row; }
  return rows.map((row,v) => {
    const removed = row | bit(v);
    let hit = 0;
    for (let w = 0; w < coreRows.length; ++w) if (!(removed & bit(w))) hit |= rows[w];
    const sources = (bit(n)-1) & ~(removed | hit);
    return rootMinimum(rows, v, sources, sources & ~multiple);
  });
}

// Cross one incoming arc of each unwanted source. All arcs leaving a retained
// source stay straight, so its targets and the root's neighbours align.
export function realizingLift(out, root, keep) {
  const { S } = inspect(out)[root];
  const flip = new Map();
  for (const s of S) {
    if (keep & bit(s)) continue;
    const parents = out[root].filter(w => out[w].includes(s));
    assert.ok(parents.length >= 2);
    flip.set(s, parents[0]);
  }
  const lift = [];
  for (const [u,row] of out.entries()) {
    for (const side of [0,1])
      lift.push(row.map(v => 2*v + (side ^ Number(flip.get(v) === u))));
  }
  return lift;
}

// Independent check via bipartite matching on the optional sources and the
// targets not already covered by mandatory sources or by the root itself.
function matchingMinimum(out, root, sources) {
  const covered = new Set(out[root]);
  const optional = [];
  for (const s of sources) {
    if (out.filter(row => row.includes(s)).length === 1) {
      for (const v of out[s]) covered.add(v);
    } else {
      optional.push(s);
    }
  }
  const owner = new Map();
  function augment(s, visited) {
    for (const v of out[s]) {
      if (covered.has(v) || visited.has(v)) continue;
      visited.add(v);
      if (!owner.has(v) || augment(owner.get(v), visited)) {
        owner.set(v,s);
        return true;
      }
    }
    return false;
  }
  for (const s of optional) augment(s, new Set());
  return covered.size - sources.length + owner.size;
}

export function checkRealizations(out) {
  const masks = out.map(row => row.reduce((m,v) => m | bit(v), 0));
  const best = minima(masks, out.length);
  const base = inspect(out);
  for (const [root,{gap,keep}] of best.entries()) {
    assert.equal(matchingMinimum(out, root, base[root].S), gap);
    const rows = inspect(realizingLift(out, root, keep));
    assert.equal(rows[2*root].gap, gap);
    assert.equal(rows[2*root+1].gap, gap);
  }
  return best.map(r => r.gap);
}
