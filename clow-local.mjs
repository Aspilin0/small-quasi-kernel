import assert from 'node:assert/strict';

export function sourcesAfterDeletingClosedOut(adj, v) {
  const n = adj.length;
  const del = new Uint8Array(n);
  del[v] = 1;
  for (const a of adj[v]) del[a] = 1;
  const hasParent = new Uint8Array(n);
  for (let u = 0; u < n; ++u) {
    if (del[u]) continue;
    for (const w of adj[u]) hasParent[w] = 1;
  }
  const S = [];
  for (let u = 0; u < n; ++u) if (!del[u] && !hasParent[u]) S.push(u);
  return S;
}

// Evaluate the minimum over all subsets of the new sources.
export function exactLstar(adj, v, maxSources = 22) {
  const S = sourcesAfterDeletingClosedOut(adj, v);
  assert.ok(S.length <= maxSources, `|S(${v})|=${S.length} exceeds subset cap ${maxSources}`);

  let bestGap = Infinity, bestF = [];
  const k = S.length;
  for (let mask = 0; mask < (1 << k); ++mask) {
    const E = new Set(adj[v]);
    let fSize = 0;
    for (let i = 0; i < k; ++i) {
      if (mask & (1 << i)) {
        ++fSize;
        for (const w of adj[S[i]]) E.add(w);
      }
    }
    const gap = E.size - fSize;
    if (gap < bestGap || (gap === bestGap && fSize < bestF.length)) {
      bestGap = gap;
      bestF = [];
      for (let i = 0; i < k; ++i) if (mask & (1 << i)) bestF.push(S[i]);
    }
  }
  return { gap: bestGap, F: bestF, S };
}

export function inspectGPlus(adj) {
  const n = adj.length;
  assert.ok(n > 0);
  const indeg = new Int32Array(n);
  for (let u = 0; u < n; ++u) {
    assert.equal(new Set(adj[u]).size, adj[u].length, `Duplicate out-neighbor at ${u}`);
    for (const w of adj[u]) {
      assert.ok(Number.isInteger(w) && w >= 0 && w < n && w !== u);
      ++indeg[w];
    }
  }
  for (let u = 0; u < n; ++u) assert.ok(indeg[u] >= 1, `Vertex ${u} is a source`);
  return adj.map((row, v) => {
    const S = sourcesAfterDeletingClosedOut(adj, v);
    const E = new Set(row);
    for (const s of S) for (const w of adj[s]) E.add(w);
    const sHitsV = E.has(v);
    const g = E.size - S.length;
    return { v, S, E: [...E], g, gPlus: g + (sHitsV ? 1 : 0), sHitsV };
  });
}

export function inducedAlpha(adj, verts) {
  const k = verts.length;
  if (k <= 1) return k;
  const conn = Array.from({ length: k }, () => new Uint8Array(k));
  const pos = new Map(verts.map((v, i) => [v, i]));
  for (let i = 0; i < k; ++i) {
    for (const w of adj[verts[i]]) {
      const j = pos.get(w);
      if (j !== undefined && j !== i) {
        conn[i][j] = 1;
        conn[j][i] = 1;
      }
    }
  }
  let best = 1;
  const chosen = [];
  function search(start) {
    if (chosen.length > best) best = chosen.length;
    if (chosen.length + (k - start) <= best) return;
    for (let i = start; i < k; ++i) {
      if (chosen.some(c => conn[i][c])) continue;
      chosen.push(i);
      search(i + 1);
      chosen.pop();
    }
  }
  search(0);
  return best;
}

export function isOriented(adj) {
  for (let u = 0; u < adj.length; ++u) {
    for (const w of adj[u]) if (adj[w].includes(u)) return false;
  }
  return true;
}

export function findLemmaA(adj) {
  const n = adj.length;
  for (let y = 0; y < n; ++y) {
    if (adj[y].length === 0) continue;
    const outY = new Set(adj[y]);
    const ext = [];
    for (let u = 0; u < n; ++u) if (u !== y && !outY.has(u) && adj[u].includes(y)) ext.push(u);
    if (ext.length === 0) return { kind: 'A0', y, u: null };
    if (ext.length === 1) {
      const u = ext[0];
      const closedU = new Set([u, ...adj[u]]);
      if (adj[y].every(w => closedU.has(w))) return { kind: 'A1', y, u };
    }
  }
  return null;
}
