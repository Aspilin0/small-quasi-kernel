import assert from 'node:assert/strict';
import { isQuasiKernel, transpose } from './shared/check.mjs';
import { inspect } from './shared/clow-check.mjs';
import { indices, referenceCore } from './shared/clow-cores.mjs';

function closedOut(out, chosen) {
  return new Set([...chosen, ...chosen.flatMap(v => out[v])]);
}

function sourcesOutside(out, removed) {
  const rest = out.map((_, v) => v).filter(v => !removed.has(v));
  const reached = new Set(rest.flatMap(v => out[v]));
  return rest.filter(v => !reached.has(v));
}

function rootStep(out, roots) {
  const sources = sourcesOutside(out, closedOut(out, roots));
  const expansion = new Set([...roots, ...sources].flatMap(v => out[v]));
  const added = [...sources, ...roots.filter(v => !expansion.has(v))];
  const removed = new Set([...roots, ...sources, ...expansion]);
  return { sources, added, removed, balance: removed.size - 2 * added.length };
}

function addSinks(core, parentSets) {
  const out = core.map(row => [...row]).concat(parentSets.map(() => []));
  parentSets.forEach((parents, i) => parents.forEach(p => out[p].push(core.length + i)));
  return out;
}

function extendAtSinks(out, sinks, chosen) {
  const covered = closedOut(out, [...closedOut(out, chosen)]);
  return [...chosen, ...sinks.filter(s => !covered.has(s))];
}

// Exhaust all source-free simple digraphs on 2..4 vertices, including 2-cycles.
// Compare the core optimum plus uncovered sinks with direct whole-graph enumeration.
let tested = 0, liftsChecked = 0;
for (let n = 2; n <= 4; ++n) {
  const vertices = Array.from({ length: n }, (_, v) => v);
  const arcs = vertices.flatMap(v => vertices.filter(w => w !== v).map(w => [v, w]));
  for (let mask = 0; mask < 2 ** arcs.length; ++mask) {
    const out = vertices.map(() => []);
    for (const i of indices(mask)) {
      const [v, w] = arcs[i];
      out[v].push(w);
    }
    const incoming = transpose(out);
    if (incoming.some(row => !row.length)) continue;
    const core = vertices.filter(v => out[v].length);
    const sinks = vertices.filter(v => !out[v].length);
    const coreIncoming = core.map(v => incoming[v].map(u => core.indexOf(u)));
    let predicted = Infinity, direct = Infinity;
    for (let subset = 0; subset < 2 ** core.length; ++subset) {
      const chosen = indices(subset);
      if (!isQuasiKernel(coreIncoming, chosen)) continue;
      const extended = extendAtSinks(out, sinks, chosen.map(i => core[i]));
      assert.ok(isQuasiKernel(incoming, extended));
      predicted = Math.min(predicted, extended.length);
    }
    for (let subset = 0; subset < 2 ** n; ++subset) {
      const chosen = indices(subset);
      if (isQuasiKernel(incoming, chosen)) direct = Math.min(direct, chosen.length);
      if (!chosen.length || chosen.some(v => out[v].some(w => chosen.includes(w)))) continue;
      const step = rootStep(out, chosen);
      const rest = vertices.filter(v => !step.removed.has(v));
      const subIncoming = rest.map(v => incoming[v].filter(u => rest.includes(u)).map(u => rest.indexOf(u)));
      // Only non-sources of the remainder need coverage. Make each omitted source
      // optional by checking coverage explicitly rather than forcing it into J.
      for (let subMask = 0; subMask < 2 ** rest.length; ++subMask) {
        const inner = indices(subMask);
        if (inner.some(i => subIncoming[i].some(j => inner.includes(j)))) continue;
        if (!subIncoming.every((parents, i) => !parents.length || inner.includes(i) ||
          parents.some(j => inner.includes(j) || subIncoming[j].some(k => inner.includes(k))))) continue;
        const jSet = inner.map(i => rest[i]);
        const kept = [...jSet, ...step.sources];
        const hits = new Set(kept.flatMap(v => out[v]));
        const lifted = [...kept, ...chosen.filter(v => !hits.has(v))];
        assert.ok(isQuasiKernel(incoming, lifted));
        assert.ok(2 * (lifted.length - jSet.length) <= step.removed.size - step.balance);
        ++liftsChecked;
      }
    }
    assert.equal(predicted, direct);
    ++tested;
  }
}
console.log('Sink extension against direct minima:', tested, 'graphs');
console.log('Independent-root lifts against the whole-graph definition:', liftsChecked);

const privatePairs = core => core.flatMap((_, v) => [[v], [v]]);
const example = addSinks(referenceCore, privatePairs(referenceCore));
assert.ok(inspect(example, 4).every(row => row.gap === 0));
const step = rootStep(example, [1, 2]);
assert.deepEqual([step.sources.length, step.removed.size, step.balance], [10, 24, 4]);
assert.ok(isQuasiKernel(transpose(example), step.added));

const choices = [[0, 1], [2, 7], [3, 6], [4, 5]];
const coveredSets = choices.map(q => closedOut(referenceCore, q));
for (const q of choices) assert.ok(isQuasiKernel(transpose(referenceCore), q));
for (let v = 0; v < 8; ++v) {
  assert.equal(choices.filter(q => q.includes(v)).length, 1);
  assert.equal(coveredSets.filter(set => set.has(v)).length, 3);
}
for (let mask = 1; mask < 256; ++mask) {
  const parents = indices(mask);
  assert.ok(coveredSets.filter(set => parents.some(v => set.has(v))).length >= 3);
}
const exampleSinks = example.map((_, i) => i).slice(8);
for (const q of choices) {
  const extended = extendAtSinks(example, exampleSinks, q);
  assert.equal(extended.length, 6);
  assert.ok(isQuasiKernel(transpose(example), extended));
}
console.log('24-vertex two-root certificate:', step.added, '; all 255 sink parent sets checked');

// Attach private paths of varied lengths and a common sink with parents at different depths.
const forest = referenceCore.map(row => [...row]);
const extendedChoices = choices.map(q => [...q]);
const distances = choices.map((q, i) =>
  referenceCore.map((_, v) => q.includes(v) ? 0 : coveredSets[i].has(v) ? 1 : 2));
const tips = [];
for (let root = 0; root < 8; ++root) {
  let parent = root;
  for (let depth = 0; depth <= root; ++depth) {
    const child = forest.length;
    forest.push([]);
    forest[parent].push(child);
    for (const [i, q] of extendedChoices.entries()) {
      const d = (distances[i][parent] + 1) % 3;
      distances[i].push(d);
      if (d === 0) q.push(child);
    }
    assert.ok(extendedChoices.filter(q => q.includes(child)).length <= 2);
    parent = child;
  }
  tips.push(parent);
}
const withMerge = addSinks(forest, [tips]);
const finalChoices = extendedChoices.map(q => extendAtSinks(withMerge, [forest.length], q));
for (const q of finalChoices) assert.ok(isQuasiKernel(transpose(withMerge), q));
assert.ok(2 * Math.min(...finalChoices.map(q => q.length)) <= withMerge.length - 4);
console.log('Forest and shared terminal sink:', withMerge.length, 'vertices;', finalChoices.map(q => q.length));

const paley = Array.from({ length: 7 }, (_, i) => [1, 2, 4].map(d => (i + d) % 7));
const obstruction = addSinks(paley, privatePairs(paley));
const leaves = obstruction.map((_, i) => i).slice(7);
const paleyQ = extendAtSinks(obstruction, leaves, [0]);
assert.equal(paleyQ.length, 7);
assert.ok(isQuasiKernel(transpose(obstruction), paleyQ));
// A tournament permits at most one core root. Enumerate all compatible sink subsets.
let rootSets = 0, best = -Infinity;
for (const coreRoots of [[], ...paley.map((_, i) => [i])]) {
  const adjacent = closedOut(obstruction, coreRoots);
  const allowed = leaves.filter(s => !adjacent.has(s));
  for (let mask = 0; mask < 2 ** allowed.length; ++mask) {
    const roots = [...coreRoots, ...indices(mask).map(i => allowed[i])];
    if (!roots.length) continue;
    best = Math.max(best, rootStep(obstruction, roots).balance);
    ++rootSets;
  }
}
assert.equal(best, -1);
console.log('21-vertex obstruction:', rootSets, 'independent root sets; best balance', best);
