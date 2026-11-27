import assert from 'node:assert/strict';
import { bit, indices, referenceCore, size } from './shared/clow-cores.mjs';
import { isQuasiKernel, transpose } from './shared/check.mjs';
import { fractionalCoverParts } from './shared/fractional-cover.mjs';

// Bitsets are only used for finite replay. All labels are below 30.
function graph(out) {
  assert.ok(out.length <= 30);
  const rows = out.map(row => row.reduce((mask, v) => mask | bit(v), 0));
  const incoming = transpose(out);
  const adj = rows.map((row, v) => incoming[v].reduce((m, w) => m | bit(w), row));
  return { rows, adj, incoming, all: bit(out.length) - 1 };
}

function neighbors(rows, set) {
  let reached = 0;
  for (let m = set; m; m &= m - 1) reached |= rows[31 - Math.clz32(m & -m)];
  return reached;
}

function largestIndependent(adj, all) {
  let best = 0;
  function visit(left, chosen) {
    if (size(left) + size(chosen) <= size(best)) return;
    if (!left) { best = chosen; return; }
    const first = left & -left;
    const v = 31 - Math.clz32(first);
    visit(left & ~first & ~adj[v], chosen | first);
    visit(left & ~first, chosen);
  }
  visit(all, 0);
  return best;
}

// Independent exhaustive matching search with the two objectives in priority order.
function preferredMatching(rows, adj, cover, independent) {
  const vertices = indices(cover);
  let bestSize = -1, bestForward = -1, best;
  const mate = rows.map(() => -1);
  function visit(i, free, count, forward) {
    if (count + vertices.length - i < bestSize) return;
    if (i === vertices.length) {
      if (count > bestSize || (count === bestSize && forward > bestForward)) {
        bestSize = count; bestForward = forward; best = [...mate];
      }
      return;
    }
    const c = vertices[i];
    for (const x of indices(adj[c] & free)) {
      mate[c] = x;
      visit(i + 1, free & ~bit(x), count + 1, forward + Number(Boolean(rows[c] & bit(x))));
    }
    mate[c] = -1;
    visit(i + 1, free, count, forward);
  }
  visit(0, independent, 0, 0);
  return best;
}

function alternatingParts(adj, all, independent, mate) {
  const cover = all & ~independent;
  let a = 0, b = 0;
  for (const c of indices(cover)) if (mate[c] < 0) a |= bit(c);
  while (true) {
    const oldA = a;
    for (const c of indices(a)) {
      const matchingEdge = mate[c] < 0 ? 0 : bit(mate[c]);
      b |= adj[c] & independent & ~matchingEdge;
    }
    for (const c of indices(cover)) if (mate[c] >= 0 && (b & bit(mate[c]))) a |= bit(c);
    if (a === oldA) break;
  }
  return { h: a | b, cSet: cover & ~a, iSet: independent & ~b };
}

// Check kernel-perfection literally on the small support, including every induced subset.
function outKernel(rows, set) {
  for (let k = set; ; k = (k - 1) & set) {
    const hit = neighbors(rows, k);
    if (!(k & hit) && !(set & ~(k | hit))) return k;
    if (!k) return -1;
  }
}

function kernelPerfect(rows, set) {
  for (let s = set; s; s = (s - 1) & set) if (outKernel(rows, s) < 0) return false;
  return true;
}

function coveringKernel(rows, all, support, weights) {
  const weight = set => indices(set).reduce((sum, v) => sum + weights[v], 0);
  let part = support;
  while (!(kernelPerfect(rows, part) && kernelPerfect(rows, support & ~part))) {
    assert.notEqual(part, 0, 'No partition into two kernel-perfect sets');
    part = (part - 1) & support;
  }
  if (2 * weight(part) < weight(support)) part = support & ~part;
  // Add one new source at a time. Lift the kernel in reverse order of addition.
  let a = part;
  const added = [];
  while (true) {
    const candidates = all & ~(a | neighbors(rows, a));
    if (!candidates) break;
    const v = 31 - Math.clz32(candidates & -candidates);
    added.push(v); a |= bit(v);
  }
  let remaining = a, k = 0;
  for (const v of added.reverse()) {
    if (!(remaining & bit(v))) continue;
    k |= bit(v);
    remaining &= ~(bit(v) | rows[v]);
  }
  const base = outKernel(rows, remaining);
  assert.ok(base >= 0);
  k |= base;
  assert.equal(part & ~(k | neighbors(rows, k)), 0);
  return k;
}

function matchingParts(rows, adj, all) {
  if (process.argv.includes('--fractional')) {
    const parts = fractionalCoverParts(adj.map(mask => indices(mask)));
    const mask = vertices => vertices.reduce((set, v) => set | bit(v), 0);
    const h = mask(parts.half), cSet = mask(parts.cover), iSet = mask(parts.independent);
    assert.equal(neighbors(adj, iSet) & ~cSet, 0);
    assert.ok(2 * size(largestIndependent(adj, h)) <= size(h));
    const mate = preferredMatching(rows, adj, cSet, iSet);
    return { h, cSet, iSet, mate };
  }
  const iMax = largestIndependent(adj, all);
  const mate = preferredMatching(rows, adj, all & ~iMax, iMax);
  return { ...alternatingParts(adj, all, iMax, mate), mate };
}

function replay(out, direct = false) {
  const { rows, adj, incoming, all } = graph(out);
  assert.ok(incoming.every(row => row.length) && out.every(row => row.length <= 4));
  const { h, cSet, iSet, mate } = matchingParts(rows, adj, all);
  let unmatched = iSet, backwardMates = 0;
  for (const c of indices(cSet)) {
    assert.ok(mate[c] >= 0 && (iSet & bit(mate[c])));
    unmatched &= ~bit(mate[c]);
    if (!(rows[c] & bit(mate[c]))) backwardMates |= bit(mate[c]);
  }
  let support = 0;
  const weights = rows.map(() => 0);
  for (const x of indices(unmatched)) {
    const p = incoming[x][0];
    assert.ok((cSet & bit(p)) && mate[p] !== x && (rows[p] & bit(mate[p])));
    support |= bit(p); ++weights[p];
  }
  for (const p of indices(support)) assert.ok(size(rows[p] & support) <= 2);
  const k = coveringKernel(rows, all, support, weights);
  assert.ok(isQuasiKernel(incoming, indices(k)));
  const hit = neighbors(rows, k);
  const coveredWeight = indices(k | hit).reduce((sum, v) => sum + weights[v], 0);
  assert.ok(2 * coveredWeight >= size(unmatched));
  let r = k;
  for (const v of indices(k & iSet & ~backwardMates)) {
    if (neighbors(rows, r & ~bit(v)) === hit) r &= ~bit(v);
  }
  const z = all & ~(r | hit | neighbors(rows, hit));
  const q = r | z;
  assert.equal(z & ~(k & iSet), 0);
  assert.ok(size(q) <= size(k & h) + size(iSet) - coveredWeight);
  assert.ok(2 * size(q) <= out.length && isQuasiKernel(incoming, indices(q)));
  if (direct) {
    let minimum = out.length;
    for (let s = 1; s <= all; ++s) {
      if (size(s) < minimum && isQuasiKernel(incoming, indices(s))) minimum = size(s);
    }
    assert.ok(minimum <= size(q) && 2 * minimum <= out.length);
  }
  return { support: size(support), chosen: indices(q) };
}

function allSourceless(n) {
  const out = Array.from({ length: n }, () => []);
  let count = 0, degreeFour = 0;
  function assign(v) {
    if (v === n) {
      replay(out, n <= 4);
      ++count;
      if (out.some(row => row.length === 4)) ++degreeFour;
      return;
    }
    const allowed = (bit(n) - 1) & ~bit(v);
    for (let s = allowed; s; s = (s - 1) & allowed) {
      const parents = indices(s);
      for (const p of parents) out[p].push(v);
      assign(v + 1);
      for (const p of parents) out[p].pop();
    }
  }
  assign(0);
  assert.equal(count, (2 ** (n - 1) - 1) ** n);
  return { count, degreeFour };
}

function privatePairs(core) {
  return core.map((row, v) => [...row, core.length + 2*v, core.length + 2*v+1])
    .concat(Array.from({ length: 2 * core.length }, () => []));
}
const tournament = Array.from({ length: 5 }, (_, i) => [(i+1)%5, (i+2)%5]);
const k5Case = replay(privatePairs(tournament));
assert.equal(k5Case.support, 5);
console.log('K5 support, 15 vertices:', k5Case);
// Within the same maximum independent set, a plain maximum matching can leave
// an induced 3-out-star on the support. The second objective removes its center.
const swapExample = [[1,2,3,5], [4,6,7], [8,9], [10,11], [0], [], [], [], [], [], [], []];
const swapGraph = graph(swapExample);
const wrongMates = [4,6,8,10];
const swapCover = 15;
assert.equal(size(largestIndependent(swapGraph.adj, swapGraph.all)), 8);
for (const [p, x] of wrongMates.entries()) assert.ok(swapGraph.adj[p] & bit(x));
const unmatchedParents = [5,7,9,11].map(x => swapGraph.incoming[x][0]);
assert.deepEqual(unmatchedParents, [0,1,2,3]);
assert.equal(size(swapGraph.rows[0] & swapCover), 3);
const preferred = preferredMatching(swapGraph.rows, swapGraph.adj, swapCover, swapGraph.all & ~swapCover);
assert.ok(indices(swapCover).every(c => swapGraph.rows[c] & bit(preferred[c])));
assert.equal(preferred[0], 5);
console.log('Matching tie-break example:', replay(swapExample, true));
console.log('24-vertex single-root obstruction:', replay(privatePairs(referenceCore)));
const noSinks = Array.from({ length: 7 }, (_, i) => [1, 2, 3, 4].map(d => (i+d)%7));
console.log('Sink-free 4-out-regular example:', replay(noSinks, true));
for (let n = 2; n <= 5; ++n) console.log('Labelled sourceless digraphs:', n, allSourceless(n));
