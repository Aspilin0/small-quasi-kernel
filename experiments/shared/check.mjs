import assert from 'node:assert/strict';

// This checker follows arcs towards the chosen set.
export function isQuasiKernel(out, chosen) {
  const q = new Set(chosen);
  if (q.size !== chosen.length || chosen.some(v => !Number.isInteger(v) || v < 0 || v >= out.length)) {
    return false;
  }
  for (const [v, next] of out.entries()) {
    const hits = next.some(w => q.has(w));
    if (q.has(v)) {
      if (hits) return false;
    } else if (!hits && !next.some(w => out[w].some(t => q.has(t)))) {
      return false;
    }
  }
  return true;
}

export function transpose(adj) {
  const rev = Array.from({ length: adj.length }, () => []);
  for (let u = 0; u < adj.length; ++u) for (const w of adj[u]) rev[w].push(u);
  return rev;
}

// Check the half bound and follow arcs from the chosen set.
export function verifySmallQuasiKernel(adj, Q) {
  const n = adj.length;
  const qSet = new Set(Q);
  assert.equal(qSet.size, Q.length, 'Duplicate vertex in Q');
  assert.ok(2 * Q.length <= n, `Quasi-kernel too large: 2*${Q.length} > ${n}`);
  for (const u of Q) {
    assert.ok(Number.isInteger(u) && u >= 0 && u < n);
    for (const w of adj[u]) assert.ok(!qSet.has(w), `Arc ${u}->${w} inside Q`);
  }
  const dist = new Int8Array(n).fill(3);
  for (const u of Q) dist[u] = 0;
  for (const u of Q) {
    for (const w of adj[u]) {
      if (dist[w] > 1) dist[w] = 1;
      for (const x of adj[w]) if (dist[x] > 2) dist[x] = 2;
    }
  }
  for (let u = 0; u < n; ++u) assert.ok(dist[u] <= 2, `Vertex ${u} not reached in <= 2 steps`);
}
