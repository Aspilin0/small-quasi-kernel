import assert from 'node:assert/strict';
import { allCores, bit, indices, orbitFilter, size } from './clow-cores.mjs';
import { checkRealizations, minima, rootMinimum } from './clow-minima.mjs';

// Remove the distinguished last vertex of a seven-vertex core. Its deletion
// can create sources and sinks, so all capped orientations on six are needed.
function augmentedCores(n, visit) {
  const k = n-1, accept = orbitFilter(k);
  const full = bit(k)-1;
  allCores(k, old => {
    if (!accept(old)) return;
    let available = 0, requireOut = 0, hit = 0;
    for (let i=0; i<k; ++i) {
      if (size(old[i]) < 3) available |= bit(i);
      if (!old[i]) requireOut |= bit(i);
      hit |= old[i];
    }
    const requireIn = full & ~hit;
    for (let fromNew = 1; fromNew <= full; ++fromNew) {
      if ((fromNew & requireIn) !== requireIn || size(fromNew)>3) continue;
      const possible = available & ~fromNew;
      for (let toNew=possible; toNew; toNew=(toNew-1)&possible) {
        if ((toNew & requireOut) !== requireOut) continue;
        const rows = old.map((row,i) => row | (toNew & bit(i) ? bit(k) : 0));
        rows.push(fromNew);
        visit(rows);
      }
    }
  }, { allowZeroDegree: true });
}

// Distinguish the unique core arc u -> p entering an indegree-one
// non-sink p. Removing both vertices leaves an arbitrary capped orientation.
function oneParentCores(n, visit) {
  const k = n-2, u = k, p = k+1, full = bit(k)-1;
  const take = orbitFilter(k);
  allCores(k, old => {
    if (!take(old)) return;
    let spare = 0, mustSend = 0, hit = 0;
    for (let i=0; i<k; ++i) {
      if (size(old[i])<3) spare |= bit(i);
      if (!old[i]) mustSend |= bit(i);
      hit |= old[i];
    }
    const mustReceive = full & ~hit;
    const rows = [...old,0,0];
    for (let fromU=0; fromU<=full; ++fromU) {
      if (size(fromU)>2 || (fromU & mustSend)) continue;
      const possible = spare & ~fromU;
      // u has to receive an arc from an old vertex. p cannot point back at u.
      for (let toU=possible; toU; toU=(toU-1)&possible) {
        if ((mustSend & toU) !== mustSend) continue;
        for (let i=0; i<k; ++i) rows[i] = old[i] | (toU & bit(i) ? bit(u) : 0);
        rows[u] = fromU | bit(p);
        for (let fromP=1; fromP<=full; ++fromP) {
          if (size(fromP)>3 || (mustReceive & ~(fromU | fromP))) continue;
          rows[p] = fromP;
          visit(rows);
        }
      }
    }
  }, {allowZeroDegree:true});
}

function search(n, generate) {
  const full = bit(n)-1;
  let cores = 0, patterns = 0, pastBound = 0, passing = 0, example;
  generate(rows => {
    ++cores;
    let eligible = 0, seen = 0, multi = 0;
    for (let v=0; v<n; ++v) {
      if (size(rows[v]) < 3) eligible |= bit(v);
      multi |= seen & rows[v]; seen |= rows[v];
    }
    patterns += 2 ** size(eligible);
    const base = [];
    for (let v=0; v<n; ++v) {
      let hit = 0;
      const removed = rows[v] | bit(v);
      for (let u=0; u<n; ++u) if (!(removed & bit(u))) hit |= rows[u];
      const sources = full & ~(removed | hit);
      const floor = rootMinimum(rows, v, sources, sources & ~multi).gap;
      // Even marking every eligible child cannot rescue this root.
      if (floor > size(rows[v] & eligible)) return;
      base.push(floor);
    }
    for (let marked=eligible;; marked=(marked-1)&eligible) {
      if (base.every((g,v) => g + Number(Boolean(marked & bit(v))) <= size(rows[v] & marked))) {
        ++pastBound;
        const actual = rows.slice();
        for (const v of indices(marked)) {
          actual[v] |= bit(actual.length);
          actual.push(0);
        }
        if (minima(actual, actual.length).every(r => r.gap <= 0)) {
          ++passing;
          if (!example) {
            example = actual.map(indices);
            assert.ok(checkRealizations(example).every(g => g <= 0));
          }
        }
      }
      if (!marked) break;
    }
  });
  return { n, cores, patterns, pastBound, passing, example };
}

// The two enumeration routes count different labellings. Survival of an
// actual instance is invariant under those labellings.
for (const n of [3,4,5]) console.log(search(n, visit => allCores(n,visit)));
for (const n of [6,7]) console.log(search(n, visit => augmentedCores(n,visit)));
if (process.argv.includes('--eight')) console.log(search(8, visit => oneParentCores(8,visit)));
