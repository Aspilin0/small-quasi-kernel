import assert from 'node:assert/strict';
import { bit, indices, referenceCore, size } from './shared/clow-cores.mjs';
import { isQuasiKernel, transpose } from './shared/check.mjs';

// Extend every labelled tournament by all orientations at the new vertex.
function extensions(rows, visit) {
  const n = rows.length, next = [...rows, 0];
  for (let mask = 0; mask < bit(n); ++mask) {
    next[n] = mask;
    for (let v = 0; v < n; ++v) next[v] = rows[v] | ((mask & bit(v)) ? 0 : bit(n));
    visit(next);
  }
}

function tournaments(n, visit) {
  if (n === 0) visit([]);
  else tournaments(n - 1, rows => extensions(rows, visit));
}

function subsetWeights(weights) {
  return Array.from({ length: bit(weights.length) }, (_, mask) =>
    indices(mask).reduce((sum, v) => sum + weights[v], 0));
}

// Search by the first element of a transitive ordering, independently of
// the triple counts, exceptional weights, and regularity used in the proof.
function hasTransitiveWeight(rows, mask, weights, sums, target) {
  if (target <= 0) return true;
  if (sums[mask] < target) return false;
  for (let left = mask; left; left &= left - 1) {
    const v = 31 - Math.clz32(left & -left);
    if (hasTransitiveWeight(rows, mask & rows[v], weights, sums, target - weights[v])) return true;
  }
  return false;
}

const unit = Array(8).fill(1), cardinality = subsetWeights(unit);
const triples = Array.from({ length: 64 }, (_, mask) => mask).filter(m => size(m) === 3 && (m & 1));
let six = 0;
tournaments(6, rows => {
  assert.ok(triples.some(m => hasTransitiveWeight(rows, m, unit, cardinality, 3) &&
    hasTransitiveWeight(rows, 63 ^ m, unit, cardinality, 3)));
  ++six;
});
assert.equal(six, 2 ** 15);

// All labels are enumerated, so fixing the locations of the heavy vertices
// covers every relabelling of both weight profiles of total nine.
const profiles = [[3,1,1,1,1,1,1], [2,2,1,1,1,1,1]].map(weights => [weights, subsetWeights(weights)]);
let seven = 0, withoutFour = 0, eightExtensions = 0;
tournaments(7, rows => {
  for (const [weights, sums] of profiles) {
    assert.ok(hasTransitiveWeight(rows, 127, weights, sums, 5));
  }
  if (!hasTransitiveWeight(rows, 127, unit, cardinality, 4)) {
    assert.ok(rows.every(mask => size(mask) === 3));
    ++withoutFour;
    extensions(rows, larger => {
      assert.ok(hasTransitiveWeight(larger, 255, unit, cardinality, 4));
      ++eightExtensions;
    });
  }
  ++seven;
});
assert.equal(seven, 2 ** 21);
assert.equal(withoutFour, 240);
assert.equal(eightExtensions, 128 * withoutFour);
console.log({ six, seven, withoutFour, eightExtensions });

// Test both the base and a nontrivial double cover. Check the merge and its
// successors on the actual digraph, with an independent minimum-size search.
function checkExtension(core, roots, expectedHits, sheets) {
  const out = [];
  for (const [u, row] of core.entries()) {
    for (let i = 0; i < sheets; ++i) {
      out.push(row.map((v, j) => sheets * v + ((i + u + j) % sheets)));
    }
  }
  const coreOrder = out.length;
  const parents = [[0, sheets], [sheets, 2 * sheets], [coreOrder, coreOrder + 1],
    [0, coreOrder + 2], [coreOrder + 2, coreOrder + 3]];
  for (const incoming of parents) {
    const child = out.length;
    out.push([]);
    for (const u of incoming) out[u].push(child);
  }
  const incoming = transpose(out);
  const hits = Array(out.length).fill(0);
  for (const base of roots) {
    const chosen = [];
    for (const u of base) for (let i = 0; i < sheets; ++i) chosen.push(sheets * u + i);
    for (let v = coreOrder; v < out.length; ++v) {
      if (!incoming[v].some(u => chosen.includes(u))) chosen.push(v);
    }
    assert.ok(isQuasiKernel(incoming, chosen));
    const reached = new Set([...chosen, ...chosen.flatMap(v => out[v])]);
    for (const v of reached) ++hits[v];
  }
  assert.ok(hits.slice(0, coreOrder).every(c => c === expectedHits));
  assert.ok(hits.slice(coreOrder).every(c => c === roots.length));
  let minimum = out.length;
  for (let mask = 0; mask < bit(out.length); ++mask) {
    if (size(mask) < minimum && isQuasiKernel(incoming, indices(mask))) minimum = size(mask);
  }
  assert.ok(2 * minimum <= out.length);
  console.log({ coreOrder, sheets, order: out.length, minimum, hitsOnCore: expectedHits, candidates: roots.length });
}

const paley = Array.from({ length: 7 }, (_, u) => [1, 2, 4].map(d => (u + d) % 7));
for (const sheets of [1, 2]) {
  checkExtension(referenceCore, [[0,1], [2,7], [3,6], [4,5]], 3, sheets);
  checkExtension(paley, paley.map((_, v) => [v]), 4, sheets);
}

// Tight seven-point coverage branch with a nontrivial return path and a digon.
// Vertices 0..6 form Paley, 7 is the hub, and 8..22 form the independent side.
const hub = 7, independent = Array.from({ length: 15 }, (_, i) => i + 8);
const boundary = paley.map((row, v) => [...row, 8 + 2*v, 9 + 2*v])
  .concat([[0, 22]], independent.map(() => [hub]));
const reverse = transpose(boundary);
function reachableFromHub(out) {
  const seen = new Set([hub]);
  for (const v of seen) for (const u of out[v]) seen.add(u);
  return seen.size;
}
assert.equal(reachableFromHub(boundary), 23);
assert.equal(reachableFromHub(reverse), 23);
assert.equal(Math.max(...boundary.map(row => row.length)), 5);
let bestSize = Infinity, bestOneStep = 0;
// A candidate uses at most one tournament vertex. Using the hub excludes
// every independent-side vertex, all of which send an arc to the hub.
for (const coreRoot of [[], ...paley.map((_, v) => [v])]) {
  for (const withHub of [false, true]) {
    const limit = withHub ? 1 : bit(independent.length);
    for (let m = 0; m < limit; ++m) {
      const chosen = withHub ? [...coreRoot, hub] : [...coreRoot, ...indices(m).map(i => independent[i])];
      if (!isQuasiKernel(reverse, chosen)) continue;
      bestSize = Math.min(bestSize, chosen.length);
      const reached = new Set([...chosen, ...chosen.flatMap(v => boundary[v])]);
      bestOneStep = Math.max(bestOneStep, paley.filter((_, v) => reached.has(v)).length);
    }
  }
}
assert.deepEqual([bestSize, bestOneStep], [7, 4]);
console.log({ strongDegreeFiveOrder: boundary.length, bestSize, bestOneStep });
