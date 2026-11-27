// The two sides are copies of the underlying undirected graph.
export function fractionalCoverParts(neighbors) {
  const n = neighbors.length;
  const rightMate = Array(n).fill(-1);
  function augment(left, seen) {
    for (const right of neighbors[left]) {
      if (seen.has(right)) continue;
      seen.add(right);
      if (rightMate[right] < 0 || augment(rightMate[right], seen)) {
        rightMate[right] = left;
        return true;
      }
    }
    return false;
  }
  for (let left = 0; left < n; ++left) augment(left, new Set());

  const matchedLeft = new Set(rightMate.filter(left => left >= 0));
  const queue = neighbors.map((_, v) => v).filter(v => !matchedLeft.has(v));
  const reachedLeft = new Set(queue);
  const reachedRight = new Set();
  for (let head = 0; head < queue.length; ++head) {
    const left = queue[head];
    for (const right of neighbors[left]) {
      if (rightMate[right] === left || reachedRight.has(right)) continue;
      reachedRight.add(right);
      const next = rightMate[right];
      if (next < 0) throw new Error('Augmenting path after maximum matching');
      if (!reachedLeft.has(next)) {
        reachedLeft.add(next);
        queue.push(next);
      }
    }
  }
  // Minimum cover: unreached left copies together with reached right copies.
  const parts = [[], [], []];
  for (let v = 0; v < n; ++v) {
    const copies = Number(!reachedLeft.has(v)) + Number(reachedRight.has(v));
    parts[copies].push(v);
  }
  return { independent: parts[0], half: parts[1], cover: parts[2] };
}
