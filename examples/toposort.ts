/**
 * Topological sort (Kahn's algorithm) — Map/Set test case.
 *
 * This is the real algorithm from CharmChat's workflow engine,
 * written in idiomatic TypeScript using Map and Set.
 * Requires LemmaScript Map/Set support to compile.
 */

export function topologicalSort(
  nodeIds: string[],
  deps: Map<string, Set<string>>,
): string[] {
  //@ requires allDistinct(nodeIds, nodeIds.length)
  //@ ensures \result.length <= nodeIds.length

  const inDegree = new Map<string, number>();
  const adjacency = new Map<string, string[]>();

  for (const id of nodeIds) {
    //@ invariant forall(k, 0 <= k && k < _id_idx ==> inDegree.has(nodeIds[k]))
    inDegree.set(id, 0);
    adjacency.set(id, []);
  }

  for (const id of nodeIds) {
    const nodeDeps = deps.get(id);
    if (nodeDeps !== undefined) {
      inDegree.set(id, nodeDeps.size);
      for (const dep of nodeDeps) {
        const adj = adjacency.get(dep);
        if (adj !== undefined) {
          adjacency.set(dep, [...adj, id]);
        }
      }
    }
  }

  const queue: string[] = [];
  for (const id of nodeIds) {
    if (inDegree.get(id) === 0) {
      queue = [...queue, id];
    }
  }

  let sorted: string[] = [];
  let qHead = 0;
  while (qHead < queue.length) {
    //@ type qHead nat
    //@ invariant qHead <= queue.length
    //@ invariant sorted.length === qHead
    //@ decreases nodeIds.length - sorted.length
    const id = queue[qHead];
    sorted = [...sorted, id];
    qHead = qHead + 1;

    const neighbors = adjacency.get(id);
    if (neighbors !== undefined) {
      for (const neighbor of neighbors) {
        const deg = inDegree.get(neighbor);
        if (deg !== undefined) {
          const newDeg = deg - 1;
          inDegree.set(neighbor, newDeg);
          if (newDeg === 0) {
            queue = [...queue, neighbor];
          }
        }
      }
    }
  }

  return sorted;
}
