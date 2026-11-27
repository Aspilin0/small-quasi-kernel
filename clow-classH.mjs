import assert from 'node:assert/strict';
import { isQuasiKernel, transpose } from './check.mjs';
import {
  exactLstar as enumerateLstar, findLemmaA, inducedAlpha,
  inspectGPlus as evaluateGPlus, isOriented, sourcesAfterDeletingClosedOut,
} from './clow-local.mjs';

export { findLemmaA, inducedAlpha, isOriented, transpose };

export function verifyQuasiKernelIndependent(adj, Q) {
  assert.ok(2 * Q.length <= adj.length, `Quasi-kernel too large: 2*${Q.length} > ${adj.length}`);
  assert.ok(isQuasiKernel(transpose(adj), Q), `Independent check.mjs rejected Q=${JSON.stringify(Q)}`);
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
  if (adj[v].length === 0) return { gap: 0, F: [], S: [], X: [] };
  const { gap, F, S } = enumerateLstar(adj, v);
  const X = new Set();
  for (const f of F) for (const w of adj[f]) if (!adj[v].includes(w)) X.add(w);
  return { gap, F, S, X: [...X] };
}

export function inspectGPlus(adj) {
  return evaluateGPlus(adj).map(({ sHitsV, ...row }) => ({ ...row, hitsV: sHitsV }));
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

// Replay Theorem 2 with the source rule and the witness from Theorem 1.
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
    const S = sourcesAfterDeletingClosedOut(adj, v);
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
