import assert from 'node:assert/strict';
import { isQuasiKernel } from './shared/check.mjs';

function subdivide(out, u, v, count) {
  const result = out.map(next => [...next]);
  const first = out.length;
  result[u][result[u].indexOf(v)] = first;
  for (let i = 0; i < count; ++i) {
    result.push([i + 1 === count ? v : first + i + 1]);
  }
  return result;
}

// Generate old solutions by marking predecessors in two rounds.
function* quasiKernels(out) {
  const all = (1 << out.length) - 1;
  const rows = out.map(next => next.reduce((mask, v) => mask | (1 << v), 0));
  const predecessors = set => rows.reduce((mask, row, v) => (row & set) ? mask | (1 << v) : mask, 0);
  for (let mask = 1; mask <= all; ++mask) {
    const near = predecessors(mask);
    if ((mask & near) || (mask | near | predecessors(near)) !== all) continue;
    yield out.map((_, v) => v).filter(v => mask & (1 << v));
  }
}

function* sinkFreeGraphs(n) {
  const rows = [];
  function* extend() {
    const u = rows.length;
    if (u === n) {
      yield rows;
      return;
    }
    for (let row = 1; row < (1 << n); ++row) {
      if (row & (1 << u)) continue;
      rows.push(Array.from({ length: n }, (_, i) => i).filter(i => row & (1 << i)));
      yield* extend();
      rows.pop();
    }
  }
  yield* extend();
}

for (const n of [2, 3, 4]) {
  let graphs = 0, solutions = 0, lifts = 0;
  for (const out of sinkFreeGraphs(n)) {
    ++graphs;
    const sets = [...quasiKernels(out)];
    // Compare the search to direct testing of every subset, including the empty set.
    let directCount = 0;
    for (let mask = 0; mask < (1 << n); ++mask) {
      const q = out.map((_, v) => v).filter(v => mask & (1 << v));
      if (isQuasiKernel(out, q)) ++directCount;
    }
    assert.equal(sets.length, directCount);
    solutions += sets.length;
    for (const q of sets) {
      assert.ok(isQuasiKernel(out, q));
      for (const [u, next] of out.entries()) {
        for (const v of next) {
          const expanded = subdivide(out, u, v, 2);
          const lifted = [...q, q.includes(v) ? n : n + 1];
          assert.ok(isQuasiKernel(expanded, lifted), JSON.stringify({ out, u, v, q, lifted }));
          ++lifts;
        }
      }
    }
  }
  assert.equal(graphs, (2 ** (n - 1) - 1) ** n);
  console.log({ n, graphs, solutions, lifts });
}

// z=0, u=1, v=2. Both ways of retaining the old choices fail after one subdivision.
const original = [[1], [2], [1]];
const once = subdivide(original, 1, 2, 1);
assert.ok(isQuasiKernel(original, [2]));
assert.ok(!isQuasiKernel(once, [2]));
assert.ok(!isQuasiKernel(once, [2, 3]));
assert.ok(isQuasiKernel(once, [1]));
console.log('Single-subdivision obstruction and alternative solution verified.');
