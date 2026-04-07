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

  // Phase 1: initialize maps
  for (const id of nodeIds) {
    //@ invariant forall(k, 0 <= k && k < _id_idx ==> inDegree.has(nodeIds[k]))
    //@ invariant forall(k, inDegree.has(k) ==> inDegree.get(k) === 0)
    //@ invariant forall(k, adjacency.has(k) ==> adjacency.get(k) === [])
    inDegree.set(id, 0);
    adjacency.set(id, []);
  }

  // Phase 2: build adjacency and in-degree from deps
  for (const id of nodeIds) {
    //@ invariant forall(k, 0 <= k && k < nodeIds.length ==> inDegree.has(nodeIds[k]))
    //@ invariant forall(k, inDegree.has(k) ==> inDegree.get(k) >= 0)
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

  // Phase 3: seed queue with zero in-degree nodes
  const queue: string[] = [];
  for (const id of nodeIds) {
    //@ invariant queue.length <= nodeIds.length
    //@ invariant queue.length <= _id_idx3
    if (inDegree.get(id) === 0) {
      queue = [...queue, id];
    }
  }

  // Phase 4: Kahn's loop
  let sorted: string[] = [];
  let qHead = 0;
  while (qHead < queue.length) {
    //@ type qHead nat
    //@ invariant qHead <= queue.length
    //@ invariant sorted.length === qHead
    //@ invariant sorted.length <= nodeIds.length
    //@ invariant queue.length <= nodeIds.length
    //@ decreases nodeIds.length - sorted.length
    const id = queue[qHead];
    sorted = [...sorted, id];
    qHead = qHead + 1;

    const neighbors = adjacency.get(id);
    if (neighbors !== undefined) {
      for (const neighbor of neighbors) {
        //@ invariant qHead <= queue.length
        //@ invariant sorted.length === qHead
        //@ invariant queue.length <= nodeIds.length
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
