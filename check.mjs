// Directly check the definition on a complete graph, independently of the lift.
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
