import assert from 'node:assert/strict';
import { isQuasiKernel } from './check.mjs';

// ============================================================================
// Independent Evaluators (decoupled from proof search / witness selection)
// ============================================================================

export function transpose(adj) {
  const rev = Array.from({ length: adj.length }, () => []);
  for (let u = 0; u < adj.length; ++u) for (const w of adj[u]) rev[w].push(u);
  return rev;
}

export function verifyQuasiKernelIndependent(adj, Q) {
  assert.ok(2 * Q.length <= adj.length, `Quasi-kernel too large: 2*${Q.length} > ${adj.length}`);
  assert.ok(isQuasiKernel(transpose(adj), Q), `Independent check.mjs rejected Q=${JSON.stringify(Q)}`);
}

export function inducedAlpha(adj, verts) {
  const k = verts.length;
  if (k <= 1) return k;
  const conn = Array.from({ length: k }, () => new Uint8Array(k));
  const pos = new Map(verts.map((v, i) => [v, i]));
  for (let i = 0; i < k; ++i) {
    for (const w of adj[verts[i]]) {
      const j = pos.get(w);
      if (j !== undefined && j !== i) { conn[i][j] = 1; conn[j][i] = 1; }
    }
  }
  let best = 1;
  const chosen = [];
  function bt(start) {
    if (chosen.length > best) best = chosen.length;
    if (chosen.length + (k - start) <= best) return;
    for (let i = start; i < k; ++i) {
      let ok = true;
      for (const c of chosen) if (conn[i][c]) { ok = false; break; }
      if (ok) { chosen.push(i); bt(i + 1); chosen.pop(); }
    }
  }
  bt(0);
  return best;
}

export function isSourcelessSimple(adj) {
  const n = adj.length;
  if (n === 0) return false;
  const indeg = new Int32Array(n);
  for (let u = 0; u < n; ++u) {
    if (new Set(adj[u]).size !== adj[u].length) return false;
    for (const w of adj[u]) {
      if (!Number.isInteger(w) || w < 0 || w >= n || w === u) return false;
      ++indeg[w];
    }
  }
  return indeg.every(d => d >= 1);
}

export function isOriented(adj) {
  for (let u = 0; u < adj.length; ++u) {
    for (const w of adj[u]) if (adj[w].includes(u)) return false;
  }
  return true;
}

export function inClassH(adj) {
  for (let u = 0; u < adj.length; ++u) {
    const d = adj[u].length;
    if (d <= 3) continue;
    const a = inducedAlpha(adj, adj[u]);
    if (a > 1 && d + a > 6) return false;
  }
  return true;
}

export function exactLstar(adj, v) {
  const n = adj.length;
  if (adj[v].length === 0) return { gap: 0, F: [], S: [], X: [] };
  const del = new Uint8Array(n);
  del[v] = 1;
  for (const a of adj[v]) del[a] = 1;
  const hasP = new Uint8Array(n);
  for (let u = 0; u < n; ++u) if (!del[u]) for (const w of adj[u]) hasP[w] = 1;
  const S = [];
  for (let u = 0; u < n; ++u) if (!del[u] && !hasP[u]) S.push(u);
  const k = S.length;
  assert.ok(k <= 22, `|S(${v})|=${k} exceeds exact subset cap`);
  let bestGap = adj[v].length, bestF = [];
  for (let mask = 1; mask < (1 << k); ++mask) {
    const E = new Set(adj[v]);
    let fSz = 0;
    for (let i = 0; i < k; ++i) {
      if (mask & (1 << i)) {
        ++fSz;
        for (const w of adj[S[i]]) E.add(w);
      }
    }
    const gap = E.size - fSz;
    if (gap < bestGap || (gap === bestGap && fSz < bestF.length)) {
      bestGap = gap;
      bestF = [];
      for (let i = 0; i < k; ++i) if (mask & (1 << i)) bestF.push(S[i]);
    }
  }
  const av = new Set(adj[v]);
  const X = new Set();
  for (const f of bestF) for (const w of adj[f]) if (!av.has(w)) X.add(w);
  return { gap: bestGap, F: bestF, S, X: [...X] };
}

export function inspectGPlus(adj) {
  assert.ok(isSourcelessSimple(adj));
  const n = adj.length;
  return adj.map((row, v) => {
    const del = new Uint8Array(n);
    del[v] = 1;
    for (const a of row) del[a] = 1;
    const hasP = new Uint8Array(n);
    for (let u = 0; u < n; ++u) if (!del[u]) for (const w of adj[u]) hasP[w] = 1;
    const S = [];
    for (let u = 0; u < n; ++u) if (!del[u] && !hasP[u]) S.push(u);
    const E = new Set(row);
    let hitsV = false;
    for (const s of S) for (const w of adj[s]) { E.add(w); if (w === v) hitsV = true; }
    const g = E.size - S.length;
    return { v, S, E: [...E], g, gPlus: g + (hitsV ? 1 : 0), hitsV };
  });
}

export function computeM(adj) {
  const n = adj.length;
  const indeg = new Int32Array(n);
  for (let u = 0; u < n; ++u) for (const w of adj[u]) ++indeg[w];
  const inI1 = indeg.map(d => d === 1);
  const inZ = adj.map(row => row.every(w => !inI1[w]));
  const c10 = new Int32Array(n);
  let M = 0;
  for (let u = 0; u < n; ++u) {
    let c = 0;
    for (const w of adj[u]) if (inI1[w] && inZ[w]) ++c;
    c10[u] = c;
    if (c > M) M = c;
  }
  return { M, c10, inI1, inZ, indeg };
}

// ============================================================================
// Constructive Witness Selector Following Theorem 1 (Class H) Branch by Branch
// ============================================================================

export function selectWitnessClassH(adj) {
  const n = adj.length;
  const isCore = adj.map(r => r.length > 0);
  const core = [];
  for (let u = 0; u < n; ++u) if (isCore[u]) core.push(u);
  assert.ok(core.length > 0);

  const ball1 = r => [r, ...adj[r]].filter(v => isCore[v]);
  const ball2 = r => {
    const s = new Set([r]);
    for (const a of adj[r]) { s.add(a); for (const b of adj[a]) s.add(b); }
    return [...s].filter(v => isCore[v]);
  };
  const ball3 = r => {
    const s = new Set(ball2(r));
    for (const x of [...s]) for (const y of adj[x]) s.add(y);
    return [...s].filter(v => isCore[v]);
  };
  const tryPick = (cands, tag) => {
    const seen = new Set();
    for (const v of cands) {
      if (!isCore[v] || seen.has(v)) continue;
      seen.add(v);
      if (exactLstar(adj, v).gap >= 1) return { v, branch: tag };
    }
    return null;
  };
  const mustPick = (cands, tag) => {
    const hit = tryPick(cands, tag);
    assert.ok(hit !== null, `Class H proof invariant violated in branch ${tag}`);
    return hit;
  };

  // Fact 2: c(v) = 0 or k(v) >= 2 -> witness in ball1(v)
  for (const v of core) {
    const k = adj[v].filter(w => !isCore[w]).length;
    if (k === adj[v].length) return mustPick([v], 'F2_c0');
    if (k >= 2) return mustPick(ball1(v), 'F2_k2');
  }

  const { M, c10 } = computeM(adj);
  assert.ok(M >= 0 && M <= 3);

  // Case M = 3: witness in ball1(u*)
  if (M === 3) {
    const uStar = core.find(u => c10[u] === 3);
    return mustPick(ball1(uStar), 'M3');
  }

  // Case M = 0:
  if (M === 0) {
    for (const v of core) {
      if (adj[v].some(w => !isCore[w])) return mustPick(ball1(v), 'M0_sink');
      if (inducedAlpha(adj, adj[v]) === 1) {
        const p = core.find(u => adj[u].includes(v));
        return mustPick(ball1(p), 'M0_typeI');
      }
      const r = exactLstar(adj, v);
      if (r.gap >= 1) return { v, branch: 'M0_direct' };
      if (r.X.length > 0) return mustPick(ball1(v), 'M0_Xpos');
    }
    let r = core[0];
    for (const u of core) if (adj[u].length < adj[r].length) r = u;
    return mustPick(ball1(r), 'M0_minDeg');
  }

  // Case M = 2:
  if (M === 2) {
    const u2s = core.filter(u => c10[u] === 2);
    for (const u of u2s) {
      if (adj[u].length <= 3) return mustPick(ball2(u), 'M2_deg23');
      if (adj[u].some(w => !isCore[w])) return mustPick(ball2(u), 'M2_k1');
      const r = exactLstar(adj, u);
      if (r.gap >= 1) return { v: u, branch: 'M2_direct' };
      if (r.X.length === 0) return mustPick(ball1(u), 'M2_deg4_X0');
    }
    for (const u of u2s) {
      const r = exactLstar(adj, u);
      if (r.X.length >= 2) return tryPick(ball2(u), 'M2_deg4_X2') || mustPick(ball3(u), 'M2_deg4_X2_b3');
    }
    const uStar = u2s[0];
    return tryPick(ball2(uStar), 'M2_deg4_X1') || mustPick(ball3(uStar), 'M2_deg4_X1_b3');
  }

  // Case M = 1:
  const sink = adj.findIndex(r => r.length === 0);
  if (sink !== -1) {
    const parents = core.filter(u => adj[u].includes(sink));
    for (const w of parents) {
      if (adj[w].length <= 3 || inducedAlpha(adj, adj[w]) >= 2) {
        return mustPick(ball2(w), 'M1_sink_nonTypeI');
      }
    }
    return mustPick([parents[0]], 'M1_sink_allTypeI');
  }
  let minDeg = Infinity, rMin = -1;
  for (const u of core) if (adj[u].length < minDeg) { minDeg = adj[u].length; rMin = u; }
  if (minDeg === 1) return mustPick(ball2(rMin), 'M1_deg1');
  if (minDeg === 2) return tryPick(ball2(rMin), 'M1_deg2') || mustPick(ball3(rMin), 'M1_deg2_b3');
  if (minDeg >= 5) return mustPick(ball1(rMin), 'M1_allTypeI');
  for (const v of core) {
    if (adj[v].length === minDeg) {
      const r = exactLstar(adj, v);
      if (r.gap >= 1) return { v, branch: `M1_d${minDeg}_direct` };
      if (r.X.length > 0) return mustPick(ball2(v), `M1_d${minDeg}_Xpos`);
    }
  }
  return mustPick(ball2(rMin), `M1_d${minDeg}_X0`);
}

// Constructive polynomial-time Small Quasi-Kernel builder for Class H (Theorem 2)
// Uses ONLY the source rule and our Theorem 1 witness v with g(v) >= L*(v) >= 1!
export function buildQuasiKernelClassH(adj) {
  function solve(verts, preCovered) {
    if (verts.length === 0) return [];
    const idxMap = new Map(verts.map((u, i) => [u, i]));
    const subAdj = verts.map(u => adj[u].filter(w => idxMap.has(w)).map(w => idxMap.get(w)));
    const m = verts.length;
    const indeg = new Int32Array(m);
    for (let i = 0; i < m; ++i) for (const j of subAdj[i]) ++indeg[j];
    for (let r = 0; r < m; ++r) {
      if (indeg[r] === 0) {
        assert.ok(preCovered.has(verts[r]));
        if (subAdj[r].length === 0) {
          const nextP = new Set(preCovered);
          nextP.delete(verts[r]);
          return solve(verts.filter((_, i) => i !== r), nextP);
        }
        const del = new Uint8Array(m);
        del[r] = 1;
        for (const a of subAdj[r]) del[a] = 1;
        const nextVerts = [], hasP = new Uint8Array(m);
        for (let i = 0; i < m; ++i) if (!del[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasP[j] = 1; }
        const nextP = new Set();
        for (let i = 0; i < m; ++i) if (!del[i] && (preCovered.has(verts[i]) || !hasP[i])) nextP.add(verts[i]);
        return [verts[r], ...solve(nextVerts, nextP)];
      }
    }
    const { v } = selectWitnessClassH(subAdj);
    const del = new Uint8Array(m);
    del[v] = 1;
    for (const a of subAdj[v]) del[a] = 1;
    const hasP = new Uint8Array(m);
    for (let i = 0; i < m; ++i) if (!del[i]) for (const j of subAdj[i]) hasP[j] = 1;
    const S = [];
    for (let i = 0; i < m; ++i) if (!del[i] && !hasP[i]) S.push(i);
    let sHitsV = false;
    const delU = new Uint8Array(m);
    delU[v] = 1;
    for (const a of subAdj[v]) delU[a] = 1;
    for (const s of S) {
      delU[s] = 1;
      for (const w of subAdj[s]) { delU[w] = 1; if (w === v) sHitsV = true; }
    }
    const nextVerts = [], hasPU = new Uint8Array(m);
    for (let i = 0; i < m; ++i) if (!delU[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasPU[j] = 1; }
    const nextP = new Set();
    for (let i = 0; i < m; ++i) if (!delU[i] && (preCovered.has(verts[i]) || !hasPU[i])) nextP.add(verts[i]);
    const Qp = solve(nextVerts, nextP);
    const qHitsV = Qp.some(q => adj[q].includes(verts[v]));
    const globalS = S.map(s => verts[s]);
    return (sHitsV || qHitsV) ? [...globalS, ...Qp] : [verts[v], ...globalS, ...Qp];
  }
  return solve(adj.map((_, i) => i), new Set());
}

// ============================================================================
// Enhanced Reduction Solver (Source + Lemma A + Lemma B + Lemma C + g+(v)>=1)
// ============================================================================

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

export function findLemmaB(adj, preCoveredSet = new Set()) {
  const n = adj.length;
  const indeg = new Int32Array(n);
  for (let u = 0; u < n; ++u) for (const w of adj[u]) ++indeg[w];
  for (let u = 0; u < n; ++u) {
    const kids = adj[u].filter(y => indeg[y] === 1);
    if (kids.length < 2) continue;
    for (let i = 0; i < kids.length; ++i) {
      for (let j = i + 1; j < kids.length; ++j) {
        const y1 = kids[i], y2 = kids[j];
        const U = new Set([y1, y2, ...adj[y1], ...adj[y2]]);
        if (!adj[u].every(x => U.has(x))) continue;
        const W = new Set([u, ...U]);
        if (W.size < 4) continue;
        const covered = preCoveredSet.has(u) || [...U].some(x => adj[x].includes(u));
        if (covered) return { kind: 'B', u, y1, y2, W: [...W] };
      }
    }
  }
  return null;
}

export function findLemmaC(adj, preCoveredSet = new Set()) {
  const n = adj.length;
  for (let v = 0; v < n; ++v) {
    if (adj[v].length === 0) continue;
    const del = new Uint8Array(n);
    del[v] = 1;
    for (const a of adj[v]) del[a] = 1;
    const hasP = new Uint8Array(n);
    for (let u = 0; u < n; ++u) if (!del[u]) for (const w of adj[u]) hasP[w] = 1;
    const S = [];
    for (let u = 0; u < n; ++u) if (!del[u] && !hasP[u]) S.push(u);
    const W = new Set([v, ...adj[v], ...S]);
    // Condition 1: N-(v) subset W
    let inOk = true;
    for (let u = 0; u < n; ++u) if (adj[u].includes(v) && !W.has(u)) { inOk = false; break; }
    if (!inOk) continue;
    // Condition 2: every new source z of H - W either in preCoveredSet or in N++(v)
    const n2v = new Set();
    for (const a of adj[v]) for (const w of adj[a]) n2v.add(w);
    const hasPW = new Uint8Array(n);
    for (let u = 0; u < n; ++u) if (!W.has(u)) for (const w of adj[u]) hasPW[w] = 1;
    let srcOk = true;
    for (let z = 0; z < n; ++z) {
      if (!W.has(z) && !hasPW[z] && !preCoveredSet.has(z) && !n2v.has(z)) { srcOk = false; break; }
    }
    if (srcOk) return { kind: 'C', v, W: [...W] };
  }
  return null;
}

export function buildQuasiKernelABC(adj, { allowA = true, allowB = true, allowC = true } = {}) {
  const usedRules = new Set();
  function solve(verts, preCovered) {
    if (verts.length === 0) return [];
    const idxMap = new Map(verts.map((u, i) => [u, i]));
    const subAdj = verts.map(u => adj[u].filter(w => idxMap.has(w)).map(w => idxMap.get(w)));
    const m = verts.length;
    const indeg = new Int32Array(m);
    for (let i = 0; i < m; ++i) for (const j of subAdj[i]) ++indeg[j];
    for (let r = 0; r < m; ++r) {
      if (indeg[r] === 0) {
        assert.ok(preCovered.has(verts[r]));
        if (subAdj[r].length === 0) {
          const nextP = new Set(preCovered);
          nextP.delete(verts[r]);
          return solve(verts.filter((_, i) => i !== r), nextP);
        }
        const del = new Uint8Array(m);
        del[r] = 1;
        for (const a of subAdj[r]) del[a] = 1;
        const nextVerts = [], hasP = new Uint8Array(m);
        for (let i = 0; i < m; ++i) if (!del[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasP[j] = 1; }
        const nextP = new Set();
        for (let i = 0; i < m; ++i) if (!del[i] && (preCovered.has(verts[i]) || !hasP[i])) nextP.add(verts[i]);
        return [verts[r], ...solve(nextVerts, nextP)];
      }
    }
    const localPre = new Set();
    for (let i = 0; i < m; ++i) if (preCovered.has(verts[i])) localPre.add(i);

    if (allowA) {
      const redA = findLemmaA(subAdj);
      if (redA) {
        usedRules.add(redA.kind);
        const del = new Uint8Array(m);
        del[redA.y] = 1;
        for (const a of subAdj[redA.y]) del[a] = 1;
        const nextVerts = [], hasP = new Uint8Array(m);
        for (let i = 0; i < m; ++i) if (!del[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasP[j] = 1; }
        const nextP = new Set();
        for (let i = 0; i < m; ++i) if (!del[i] && (preCovered.has(verts[i]) || !hasP[i])) nextP.add(verts[i]);
        const Qp = solve(nextVerts, nextP);
        if (redA.u !== null && Qp.includes(verts[redA.u])) return Qp;
        return [verts[redA.y], ...Qp];
      }
    }
    if (allowB) {
      const redB = findLemmaB(subAdj, localPre);
      if (redB) {
        usedRules.add('B');
        const del = new Uint8Array(m);
        for (const w of redB.W) del[w] = 1;
        const nextVerts = [], hasP = new Uint8Array(m);
        for (let i = 0; i < m; ++i) if (!del[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasP[j] = 1; }
        const nextP = new Set();
        for (let i = 0; i < m; ++i) if (!del[i] && (preCovered.has(verts[i]) || !hasP[i])) nextP.add(verts[i]);
        return [verts[redB.y1], verts[redB.y2], ...solve(nextVerts, nextP)];
      }
    }
    if (allowC) {
      const redC = findLemmaC(subAdj, localPre);
      if (redC) {
        usedRules.add('C');
        const del = new Uint8Array(m);
        for (const w of redC.W) del[w] = 1;
        const nextVerts = [], hasP = new Uint8Array(m);
        for (let i = 0; i < m; ++i) if (!del[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasP[j] = 1; }
        const nextP = new Set();
        for (let i = 0; i < m; ++i) if (!del[i] && (preCovered.has(verts[i]) || !hasP[i])) nextP.add(verts[i]);
        return [verts[redC.v], ...solve(nextVerts, nextP)];
      }
    }
    const rows = inspectGPlus(subAdj);
    const hit = rows.find(r => subAdj[r.v].length > 0 && r.gPlus >= 1);
    assert.ok(hit !== undefined, 'No reduction A/B/C and no g+(v)>=1 vertex found');
    usedRules.add('gPlus');
    const delU = new Uint8Array(m);
    delU[hit.v] = 1;
    for (const a of subAdj[hit.v]) delU[a] = 1;
    for (const s of hit.S) { delU[s] = 1; for (const w of subAdj[s]) delU[w] = 1; }
    const nextVerts = [], hasPU = new Uint8Array(m);
    for (let i = 0; i < m; ++i) if (!delU[i]) { nextVerts.push(verts[i]); for (const j of subAdj[i]) hasPU[j] = 1; }
    const nextP = new Set();
    for (let i = 0; i < m; ++i) if (!delU[i] && (preCovered.has(verts[i]) || !hasPU[i])) nextP.add(verts[i]);
    const Qp = solve(nextVerts, nextP);
    const qHitsV = Qp.some(q => adj[q].includes(verts[hit.v]));
    const globalS = hit.S.map(s => verts[s]);
    return (hit.hitsV || qHitsV) ? [...globalS, ...Qp] : [verts[hit.v], ...globalS, ...Qp];
  }
  const Q = solve(adj.map((_, i) => i), new Set());
  return { Q, usedRules: [...usedRules] };
}

// ============================================================================
// 1. Exhaustive Small-Graph Verification for Class H
// ============================================================================
console.log('=== 1. Exhaustive Small-Graph Verification for Class H ===');

// (1a) ALL sourceless oriented digraphs on n = 3, 4, 5 vertices in Class H,
//      PLUS all 5-vertex oriented core orbits + arbitrary 0/1 sinks in Class H (exercises oriented d+=4!)
{
  let totalChecked = 0;
  for (const n of [3, 4, 5]) {
    const pairs = [];
    for (let i = 0; i < n; ++i) for (let j = i + 1; j < n; ++j) pairs.push([i, j]);
    const adj = Array.from({ length: n }, () => []);
    const indeg = new Int32Array(n);
    function dfs(p) {
      if (p === pairs.length) {
        for (let u = 0; u < n; ++u) if (indeg[u] === 0) return;
        if (!inClassH(adj)) return;
        const { v } = selectWitnessClassH(adj);
        assert.ok(exactLstar(adj, v).gap >= 1);
        const Q = buildQuasiKernelClassH(adj);
        verifyQuasiKernelIndependent(adj, Q);
        ++totalChecked;
        return;
      }
      const [i, j] = pairs[p];
      dfs(p + 1);
      adj[i].push(j); ++indeg[j]; dfs(p + 1); adj[i].pop(); --indeg[j];
      adj[j].push(i); ++indeg[i]; dfs(p + 1); adj[j].pop(); --indeg[i];
    }
    dfs(0);
  }
  // 5-vertex oriented sourceless core orbits + arbitrary 0/1 private/shared sinks in Class H
  const n5 = 5;
  const pairs5 = [];
  for (let i = 0; i < n5; ++i) for (let j = i + 1; j < n5; ++j) pairs5.push([i, j]);
  const perms5 = [];
  (function genP(cur, used) {
    if (cur.length === n5) { perms5.push(cur); return; }
    for (let i = 0; i < n5; ++i) if (!(used & (1 << i))) genP([...cur, i], used | (1 << i));
  })([], 0);
  const seen5 = new Set();
  const core5 = Array.from({ length: n5 }, () => []);
  const indeg5 = new Int32Array(n5);
  let core5Classes = 0, orient5WithSinks = 0, orient5Deg4 = 0;
  function canon5(g) {
    let best = '';
    for (const p of perms5) {
      let s = '';
      for (let u = 0; u < n5; ++u) {
        let mask = 0;
        for (const w of g[p[u]]) mask |= (1 << p.indexOf(w));
        s += mask.toString(32);
      }
      if (!best || s < best) best = s;
    }
    return best;
  }
  function dfs5(p) {
    if (p === pairs5.length) {
      for (let u = 0; u < n5; ++u) if (indeg5[u] === 0 || core5[u].length === 0) return;
      const key = canon5(core5);
      if (seen5.has(key)) return;
      seen5.add(key);
      ++core5Classes;
      const attach = Array(n5).fill(0);
      function dfsSink(u, numSinks) {
        if (u === n5) {
          const adj = Array.from({ length: n5 + numSinks }, (_, i) => i < n5 ? [...core5[i]] : []);
          for (let i = 0; i < n5; ++i) if (attach[i] > 0) adj[i].push(n5 + attach[i] - 1);
          if (!inClassH(adj)) return;
          const { v } = selectWitnessClassH(adj);
          assert.ok(exactLstar(adj, v).gap >= 1);
          const Q = buildQuasiKernelClassH(adj);
          verifyQuasiKernelIndependent(adj, Q);
          ++orient5WithSinks;
          if (adj.some(r => r.length >= 4)) ++orient5Deg4;
          return;
        }
        attach[u] = 0;
        dfsSink(u + 1, numSinks);
        for (let s = 1; s <= numSinks + 1; ++s) {
          attach[u] = s;
          dfsSink(u + 1, Math.max(numSinks, s));
        }
      }
      dfsSink(0, 0);
      return;
    }
    const [i, j] = pairs5[p];
    dfs5(p + 1);
    core5[i].push(j); ++indeg5[j]; dfs5(p + 1); core5[i].pop(); --indeg5[j];
    core5[j].push(i); ++indeg5[i]; dfs5(p + 1); core5[j].pop(); --indeg5[i];
  }
  dfs5(0);
  console.log(`Exhaustive oriented Class H (n=3..5): ${totalChecked} digraphs passed.`);
  console.log(`Exhaustive 5v oriented core orbits (${core5Classes}) + arbitrary 0/1 sinks in Class H: ${orient5WithSinks} digraphs passed (${orient5Deg4} with d+=4).`);
}

// (1b) ALL sourceless general (2-cycle allowed) 4-vertex cores + up to 1 private/shared sink in Class H
//      (exhaustively exercises (4, 1) and (4, 2) with 2-cycles on 4..8 vertices!)
{
  const n = 4;
  const pairs = [];
  for (let i = 0; i < n; ++i) for (let j = i + 1; j < n; ++j) pairs.push([i, j]);
  // Orbit representatives under S_4 to keep runtime fast (~1s) while covering ALL isomorphism classes!
  const perms = [];
  (function genPerm(cur, used) {
    if (cur.length === n) { perms.push(cur); return; }
    for (let i = 0; i < n; ++i) if (!(used & (1 << i))) genPerm([...cur, i], used | (1 << i));
  })([], 0);
  const seen = new Set();
  let coreClasses = 0, totalWithSinks = 0, deg4Cases = 0;
  const core = Array.from({ length: n }, () => []);
  const indeg = new Int32Array(n);
  function canon(g) {
    let best = '';
    for (const p of perms) {
      let s = '';
      for (let u = 0; u < n; ++u) {
        let mask = 0;
        for (const w of g[p[u]]) mask |= (1 << p.indexOf(w));
        s += mask.toString(16);
      }
      if (!best || s < best) best = s;
    }
    return best;
  }
  function dfsCore(p) {
    if (p === pairs.length) {
      for (let u = 0; u < n; ++u) if (indeg[u] === 0 || core[u].length === 0) return;
      const key = canon(core);
      if (seen.has(key)) return;
      seen.add(key);
      ++coreClasses;
      // Attach 0 or 1 sink per core vertex (all partitions into shared/private sinks)
      const attach = Array(n).fill(0);
      function dfsSink(u, numSinks) {
        if (u === n) {
          const adj = Array.from({ length: n + numSinks }, (_, i) => i < n ? [...core[i]] : []);
          for (let i = 0; i < n; ++i) if (attach[i] > 0) adj[i].push(n + attach[i] - 1);
          if (!inClassH(adj)) return;
          const { v } = selectWitnessClassH(adj);
          assert.ok(exactLstar(adj, v).gap >= 1);
          const Q = buildQuasiKernelClassH(adj);
          verifyQuasiKernelIndependent(adj, Q);
          ++totalWithSinks;
          if (adj.some(r => r.length >= 4)) ++deg4Cases;
          return;
        }
        attach[u] = 0;
        dfsSink(u + 1, numSinks);
        for (let s = 1; s <= numSinks + 1; ++s) {
          attach[u] = s;
          dfsSink(u + 1, Math.max(numSinks, s));
        }
      }
      dfsSink(0, 0);
      return;
    }
    const [i, j] = pairs[p];
    dfsCore(p + 1);
    core[i].push(j); ++indeg[j]; dfsCore(p + 1); core[i].pop(); --indeg[j];
    core[j].push(i); ++indeg[i]; dfsCore(p + 1); core[j].pop(); --indeg[i];
    core[i].push(j); core[j].push(i); ++indeg[i]; ++indeg[j]; dfsCore(p + 1);
    core[i].pop(); core[j].pop(); --indeg[i]; --indeg[j];
  }
  dfsCore(0);
  console.log(`Exhaustive 4v general core orbits (${coreClasses}) + arbitrary 0/1 sinks in Class H: ${totalWithSinks} digraphs passed (${deg4Cases} with d+=4).`);
}

// ============================================================================
// 2. Diverse & Adversarial Verification of Class H (5,000+ hybrid digraphs)
// ============================================================================
console.log('\n=== 2. Diverse & Adversarial Class H Verification ===');

// Explicit tight Class H instances on the boundary d+(u) + alpha(u) = 6:
{
  const tightCases = [
    // K_3^* + 6 leaves (9v, d+=4, alpha=2, M=2)
    ['K_3^* + 6 leaves (9v)', [[1,2,3,4],[0,2,5,6],[0,1,7,8],[1,2],[1,2],[0,2],[0,2],[0,1],[0,1]]],
    // K_3^* + 3 leaves + 3 sinks (9v, d+=4, alpha=2, M=2, k=1)
    ['K_3^* + 3 leaves + 3 sinks (9v)', [[1,2,3,4],[0,2,5,6],[0,1,7,8],[1,2],[],[0,2],[],[0,1],[]]],
    // T_5 + 10 leaves (15v, oriented, d+=4, alpha=2, M=2)
    ['T_5 + 10 leaves (15v)', Array.from({ length: 15 }, (_, i) => i < 5
      ? [(i + 1) % 5, (i + 2) % 5, 5 + 2 * i, 6 + 2 * i]
      : [(((i - 5) >> 1) + 1) % 5, (((i - 5) >> 1) + 2) % 5])],
    // QR_7 + 7 private sinks (14v, oriented, d+=4, alpha=2, M=1, no two disjoint QKs!)
    ['QR_7 + 7 sinks (14v)', Array.from({ length: 14 }, (_, i) => i < 7
      ? [(i + 1) % 7, (i + 2) % 7, (i + 4) % 7, 7 + i] : [])],
    // K_4^* + 4 leaves + 4 sinks (12v, hybrid (4,1) + (4,2), M=1)
    ['K_4^* + 4 leaves + 4 sinks (12v)', Array.from({ length: 12 }, (_, i) => i < 4
      ? [0,1,2,3].filter(j => j !== i).concat([4 + i])
      : (i < 8 ? [0,1,2,3].filter(j => j !== (i - 4)).concat([4 + i]) : []))],
  ];
  for (const [name, adj] of tightCases) {
    assert.ok(isSourcelessSimple(adj) && inClassH(adj), `${name} not in Class H`);
    const res = selectWitnessClassH(adj);
    assert.ok(exactLstar(adj, res.v).gap >= 1);
    const Q = buildQuasiKernelClassH(adj);
    verifyQuasiKernelIndependent(adj, Q);
    console.log(`  Tight Class H instance "${name}": witness v=${res.v} (${res.branch}), |Q|=${Q.length}/${adj.length}.`);
  }
}
let seed = 20261127;
const rand = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 4294967296; };
const randInt = k => Math.floor(rand() * k);

const branchCounts = new Map();
let hybridCount = 0;
for (let t = 0; t < 5000; ++t) {
  const mode = t % 6;
  let adj;
  if (mode === 0) {
    const n = 4 + randInt(14);
    const oriented = rand() < 0.4;
    adj = Array.from({ length: n }, () => []);
    for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n);
    for (let s = 0; s < n * 6; ++s) {
      const u = randInt(n), w = randInt(n);
      if (u === w || adj[u].includes(w) || (oriented && adj[w].includes(u))) continue;
      adj[u].push(w);
      if (!inClassH(adj)) adj[u].pop();
    }
    if (rand() < 0.45) {
      for (let u = 0; u < n; ++u) {
        if (rand() < 0.3) {
          const z = adj.length;
          adj.push([]);
          adj[u].push(z);
          if (!inClassH(adj)) { adj[u].pop(); adj.pop(); }
        }
      }
    }
  } else if (mode === 1) {
    // M = 0 mixed degrees (2,3,4 and high-degree Type I)
    const n = 5 + randInt(11);
    adj = Array.from({ length: n }, () => []);
    for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n, (i + 2) % n);
    for (let s = 0; s < n * 5; ++s) {
      const u = randInt(n), w = randInt(n);
      if (u === w || adj[u].includes(w)) continue;
      adj[u].push(w);
      if (!inClassH(adj)) adj[u].pop();
    }
  } else if (mode === 2) {
    // M = 2 deg-4 rich cores + leaves/sinks
    const m = 3 + randInt(6);
    adj = Array.from({ length: m }, () => []);
    for (let i = 0; i < m; ++i) adj[i].push((i + 1) % m, (i + 2) % m);
    for (let i = 0; i < m; ++i) {
      if (rand() < 0.75) {
        const y1 = adj.length, y2 = adj.length + 1;
        adj.push([], []);
        const coreOut = [...adj[i]];
        adj[i].push(y1, y2);
        adj[y1] = [...coreOut];
        adj[y2] = rand() < 0.5 ? [...coreOut] : [];
        if (rand() < 0.4) { const extra = randInt(m); if (!adj[y1].includes(extra)) adj[y1].push(extra); }
        if (!inClassH(adj)) { adj[i].splice(-2); adj.splice(-2); }
      }
    }
  } else if (mode === 3) {
    // High-degree Type I (d+ up to 11!) + Type II/III attachments
    const m = 6 + randInt(6);
    adj = Array.from({ length: m }, () => []);
    for (let i = 0; i < m; ++i) {
      for (let j = i + 1; j < m; ++j) {
        const r = randInt(3);
        if (r === 0) adj[i].push(j);
        else if (r === 1) adj[j].push(i);
        else { adj[i].push(j); adj[j].push(i); }
      }
    }
    if (!isSourcelessSimple(adj)) continue;
    if (rand() < 0.5) {
      const z = adj.length;
      adj.push([]);
      for (let i = 0; i < m; ++i) adj[i].push(z);
    }
    for (let k = 0; k < 3; ++k) {
      const id = adj.length;
      adj.push([]);
      const p = randInt(m);
      adj[p].push(id);
      for (let c = 0; c < 3; ++c) {
        const target = randInt(m);
        if (!adj[id].includes(target)) adj[id].push(target);
      }
      if (!inClassH(adj)) { adj[p].pop(); adj.pop(); }
    }
  } else if (mode === 4) {
    // M = 3 / Fact-2 k=2 targeted: 3-out + private sinks
    const m = 4 + randInt(6);
    adj = Array.from({ length: m }, () => []);
    for (let i = 0; i < m; ++i) adj[i].push((i + 1) % m);
    for (let u = 0; u < m; ++u) {
      const add = randInt(3);
      for (let s = 0; s < add; ++s) {
        const id = adj.length;
        adj.push([]);
        adj[u].push(id);
        if (rand() < 0.4) adj[id].push((u + 1) % m, (u + 2) % m);
        if (!inClassH(adj)) { adj[u].pop(); adj.pop(); }
      }
    }
  } else {
    // Dense (4,2) general digraphs
    const n = 5 + randInt(11);
    adj = Array.from({ length: n }, () => []);
    for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n, (i + 2) % n);
    for (let s = 0; s < n * 8; ++s) {
      const u = randInt(n), w = randInt(n);
      if (u === w || adj[u].includes(w) || adj[u].length >= 4) continue;
      adj[u].push(w);
      if (!inClassH(adj)) adj[u].pop();
    }
  }
  if (!isSourcelessSimple(adj) || !inClassH(adj)) continue;
  const res = selectWitnessClassH(adj);
  assert.ok(exactLstar(adj, res.v).gap >= 1);
  const Q = buildQuasiKernelClassH(adj);
  verifyQuasiKernelIndependent(adj, Q);
  branchCounts.set(res.branch, (branchCounts.get(res.branch) || 0) + 1);
  ++hybridCount;
}
console.log(`Hybrid Class H verification: ${hybridCount} digraphs passed constructive L*>=1 & independent small QK check.`);
console.log('Proof branches exercised:', Object.fromEntries([...branchCounts.entries()].sort()));

// ============================================================================
// 3. Verify Negative Resolution of Priority 3: Oriented (4,3) Counterexamples
// ============================================================================
console.log('\n=== 3. Verifying Oriented (4,3) Counterexamples to g>=1 and g+>=1 ===');

function exactMinQuasiKernelOnSinksCore(core, sinks) {
  const m = core.length;
  let best = Infinity, bestJ = null;
  for (let mask = 1; mask < (1 << m); ++mask) {
    let ok = true, sz = 0;
    for (let i = 0; i < m && ok; ++i) {
      if (mask & (1 << i)) {
        ++sz;
        for (const j of core[i]) if (mask & (1 << j)) { ok = false; break; }
      }
    }
    if (!ok) continue;
    const d = new Int8Array(m).fill(3);
    for (let i = 0; i < m; ++i) if (mask & (1 << i)) d[i] = 0;
    for (let i = 0; i < m; ++i) if (d[i] === 0) for (const j of core[i]) {
      if (d[j] > 1) d[j] = 1;
      for (const k of core[j]) if (d[k] > 2) d[k] = 2;
    }
    if (d.some(x => x > 2)) continue;
    let cost = sz;
    for (let i = 0; i < m; ++i) if (d[i] === 2) cost += sinks[i];
    if (cost < best) {
      best = cost;
      bestJ = [];
      for (let i = 0; i < m; ++i) if (mask & (1 << i)) bestJ.push(i);
    }
  }
  return { best, bestJ };
}

for (const [m, expectMaxG, expectMaxGP] of [[3, 0, 1], [4, 0, 0], [5, 0, 0]]) {
  const coreN = 5 + m;
  const core = Array.from({ length: coreN }, () => []);
  const sinks = Array(coreN).fill(0);
  for (let i = 0; i < 5; ++i) {
    core[i] = [(i + 1) % 5, (i + 2) % 5];
    sinks[i] = 2;
  }
  for (let j = 0; j < m; ++j) {
    core[5 + j] = [5 + ((j + 1) % m), j % 5, (j + 1) % 5, (j + 2) % 5];
  }
  const adj = core.map(r => [...r]);
  for (let u = 0; u < coreN; ++u) {
    for (let s = 0; s < sinks[u]; ++s) {
      const id = adj.length;
      adj.push([]);
      adj[u].push(id);
    }
  }
  assert.ok(isSourcelessSimple(adj));
  assert.ok(isOriented(adj));
  assert.equal(Math.max(...adj.map(r => r.length)), 4);
  assert.equal(Math.max(...adj.map(r => inducedAlpha(adj, r))), 3);
  const rows = inspectGPlus(adj);
  assert.equal(Math.max(...rows.map(r => r.g)), expectMaxG);
  assert.equal(Math.max(...rows.map(r => r.gPlus)), expectMaxGP);
  for (let v = 0; v < coreN; ++v) assert.ok(exactLstar(adj, v).gap <= 0);
  const { best, bestJ } = exactMinQuasiKernelOnSinksCore(core, sinks);
  // Build full Q and verify independently via check.mjs
  const d = new Int8Array(coreN).fill(3);
  for (const u of bestJ) d[u] = 0;
  for (const u of bestJ) for (const w of core[u]) if (d[w] > 1) d[w] = 1;
  const fullQ = [...bestJ];
  for (let i = 0; i < 5; ++i) if (d[i] > 1) fullQ.push(coreN + 2 * i, coreN + 2 * i + 1);
  assert.equal(fullQ.length, best);
  verifyQuasiKernelIndependent(adj, fullQ);
  console.log(`Verified oriented (4,3) T_5 + C_${m} + 10 sinks (${adj.length}v): max g=${expectMaxG}, max g+=${expectMaxGP}, L*<=0 everywhere, q(D)=${best}/${adj.length}.`);
}

// Also verify the 22-vertex oriented (4,3) graph with strictly negative g+ = -1 on 4 vertices
{
  const core10 = [[2,9,3,1],[3,4],[6,3,7,4],[4,5],[5,6],[9,6],[9,3],[4,1,8,9],[4,0,5,3],[1,3]];
  const sinks10 = [0, 2, 0, 2, 2, 2, 2, 0, 0, 2];
  const adj = core10.map(r => [...r]);
  const sinkStart = [];
  for (let u = 0; u < 10; ++u) {
    sinkStart.push(adj.length);
    for (let s = 0; s < sinks10[u]; ++s) { const id = adj.length; adj.push([]); adj[u].push(id); }
  }
  assert.ok(isSourcelessSimple(adj) && isOriented(adj));
  assert.equal(Math.max(...adj.map(r => r.length)), 4);
  assert.equal(Math.max(...adj.map(r => inducedAlpha(adj, r))), 3);
  const rows = inspectGPlus(adj);
  assert.equal(Math.max(...rows.map(r => r.g)), 0);
  assert.equal(Math.max(...rows.map(r => r.gPlus)), 0);
  assert.equal(rows.filter(r => r.gPlus === -1).length, 4);
  const { best, bestJ } = exactMinQuasiKernelOnSinksCore(core10, sinks10);
  const d = new Int8Array(10).fill(3);
  for (const u of bestJ) d[u] = 0;
  for (const u of bestJ) for (const w of core10[u]) if (d[w] > 1) d[w] = 1;
  const fullQ = [...bestJ];
  for (let u = 0; u < 10; ++u) if (d[u] > 1) for (let s = 0; s < sinks10[u]; ++s) fullQ.push(sinkStart[u] + s);
  assert.equal(fullQ.length, best);
  verifyQuasiKernelIndependent(adj, fullQ);
  console.log(`Verified 22v oriented (4,3) counterexample: 4 core vertices g=g+=-1, rest 0, q(D)=${best}/22.`);
}

// ============================================================================
// 4. Verify New M = 1 alpha+ = 2 Family, Lemma B on CP_8^* + 16 leaves,
//    and Universal (d-1)/d Independent Set Bound!
// ============================================================================
console.log('\n=== 4. Verifying M=1 alpha+=2 Obstruction, Lemma B/C, and (d-1)/d Bound ===');

// (4a) K_{2r}^* + 2r sinks + r pair-vertices (5r vertices, r=4,5,6)
for (const r of [4, 5, 6]) {
  const m = 2 * r;
  const adj = Array.from({ length: 5 * r }, () => []);
  // 0..m-1: K_{2r}^*; m..2m-1: private sinks; 2m..2m+r-1: pair-vertices s_k
  for (let i = 0; i < m; ++i) {
    const rest = Array.from({ length: m }, (_, j) => j).filter(j => j !== i);
    const pairV = 2 * m + (i >> 1);
    adj[i] = [...rest, m + i, pairV];
  }
  for (let k = 0; k < r; ++k) {
    adj[2 * m + k] = Array.from({ length: m }, (_, j) => j);
  }
  assert.ok(isSourcelessSimple(adj));
  assert.equal(Math.max(...adj.map(row => inducedAlpha(adj, row))), 2);
  assert.equal(computeM(adj).M, 1);
  const rows = inspectGPlus(adj);
  for (let i = 0; i < m; ++i) {
    assert.equal(rows[i].g, 4 - r);
    assert.equal(rows[i].gPlus, 5 - r);
  }
  for (let k = 0; k < r; ++k) {
    assert.equal(rows[2 * m + k].g, 1 - r);
    assert.equal(rows[2 * m + k].gPlus, 1 - r);
  }
  // Verify Lemma C solves it with |Q| = 1 (and Lemma A0 also solves it!)
  const resC = buildQuasiKernelABC(adj, { allowA: false, allowB: false, allowC: true });
  verifyQuasiKernelIndependent(adj, resC.Q);
  assert.equal(resC.Q.length, 1);
  const resA = buildQuasiKernelABC(adj, { allowA: true, allowB: false, allowC: false });
  verifyQuasiKernelIndependent(adj, resA.Q);
  console.log(`Verified M=1 alpha+=2 K_${m}^* + ${m} sinks + ${r} pairs (${5 * r}v): core g=${4 - r}, g+=${5 - r}, pair g=g+=${1 - r}; Lemma C => |Q|=${resC.Q.length}/${5 * r}.`);
}

// (4b) Lemma B solves Lemma-A-irreducible CP_8^* + 16 leaves (24v)!
{
  const m = 8;
  const adj = Array.from({ length: 3 * m }, () => []);
  for (let i = 0; i < m; ++i) {
    const partner = i ^ 1;
    const outC = Array.from({ length: m }, (_, j) => j).filter(j => j !== i && j !== partner);
    const allExceptI = Array.from({ length: m }, (_, j) => j).filter(j => j !== i);
    adj[i] = [...outC, m + 2 * i, m + 2 * i + 1];
    adj[m + 2 * i] = [...allExceptI];
    adj[m + 2 * i + 1] = [...allExceptI];
  }
  assert.equal(findLemmaA(adj), null);
  const { Q, usedRules } = buildQuasiKernelABC(adj, { allowA: true, allowB: true, allowC: false });
  verifyQuasiKernelIndependent(adj, Q);
  console.log(`Verified Lemma B solves Lemma-A-irreducible CP_8^* + 16 leaves (24v): rules=${JSON.stringify(usedRules)}, |Q|=${Q.length}/24.`);
}

// (4c) Universal independent-set bound |I| <= ((d-1)/d)*n for alpha+(D) <= d-1 (d=2,3,4)
{
  let checked = 0;
  for (const d of [2, 3, 4]) {
    const k = d - 1;
    for (let t = 0; t < 400; ++t) {
      const n = 5 + randInt(10);
      const adj = Array.from({ length: n }, () => []);
      for (let i = 0; i < n; ++i) adj[i].push((i + 1) % n);
      for (let s = 0; s < n * 5; ++s) {
        const u = randInt(n), w = randInt(n);
        if (u === w || adj[u].includes(w)) continue;
        adj[u].push(w);
        if (inducedAlpha(adj, adj[u]) > k) adj[u].pop();
      }
      // Verify max independent set alpha(D) <= ((d-1)/d) * n
      const allV = Array.from({ length: n }, (_, i) => i);
      const alphaG = inducedAlpha(adj, allV);
      assert.ok(d * alphaG <= (d - 1) * n, `Bound violated: d=${d}, alpha=${alphaG}, n=${n}`);
      ++checked;
    }
  }
  console.log(`Verified universal alpha(D) <= ((d-1)/d)n bound on ${checked} sourceless general digraphs (d=2,3,4).`);
}

console.log('\nALL CLASS H & COUNTEREXAMPLE VERIFICATIONS PASSED!');
