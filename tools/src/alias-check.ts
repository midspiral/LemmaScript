/**
 * Pure live-alias conflict kernel for Milestone 3b
 * (`midspiral/LemmaScript#387`, `robertpenner/LemmaScript#50`).
 *
 * Kept strictly inside the LemmaScript subset so its core conflict-detection
 * and alias-binding contracts are self-verified via
 * `npx lsc check --backend=dafny tools/src/alias-check.ts`.
 */

//@ pure
export function lookupAliasGroup(aliases: Map<string, number>, name: string): number {
  const g = aliases.get(name);
  return g !== undefined ? g : -1;
}

/** Bind `name` to a fresh alias group `groupId` (breaking any prior alias). */
//@ ensures \result.has(name)
//@ ensures \result.get(name) == groupId
export function bindFreshGroup(aliases: Map<string, number>, name: string, groupId: number): Map<string, number> {
  const next = new Map<string, number>(aliases);
  next.set(name, groupId);
  return next;
}

/** Bind `dst` to share `src`'s alias group if `src` is tracked, else `fallbackId`. */
//@ ensures \result.has(dst)
export function bindCopyGroup(
  aliases: Map<string, number>,
  dst: string,
  src: string,
  fallbackId: number,
): Map<string, number> {
  const next = new Map<string, number>(aliases);
  const srcGroup = aliases.get(src);
  if (srcGroup !== undefined) {
    next.set(dst, srcGroup);
  } else {
    next.set(dst, fallbackId);
  }
  return next;
}

/**
 * Find the first candidate variable `other` that:
 *   1. is distinct from `mutatedVar`,
 *   2. is live after the mutation (`liveAfter.has(other)`), and
 *   3. shares the same non-negative alias group ID as `mutatedVar`.
 *
 * Returns `""` when no live alias conflict exists (covering both read-only
 * aliases when no mutation occurs and dead-source moves where the aliased
 * variable is not in `liveAfter`).
 */
//@ ensures \result != "" ==> \result != mutatedVar && liveAfter.has(\result)
export function findLiveAliasConflict(
  mutatedVar: string,
  aliases: Map<string, number>,
  liveAfter: Set<string>,
  candidates: string[],
): string {
  const mutGroup = aliases.get(mutatedVar);
  if (mutGroup === undefined) return "";
  let i = 0;
  while (i < candidates.length) {
    //@ invariant 0 <= i && i <= candidates.length
    const cand = candidates[i];
    if (cand !== mutatedVar && liveAfter.has(cand)) {
      const candGroup = aliases.get(cand);
      if (candGroup !== undefined && candGroup === mutGroup) {
        return cand;
      }
    }
    i = i + 1;
  }
  return "";
}

/** Boolean wrapper over `findLiveAliasConflict`. */
export function hasLiveAliasConflict(
  mutatedVar: string,
  aliases: Map<string, number>,
  liveAfter: Set<string>,
  candidates: string[],
): boolean {
  return findLiveAliasConflict(mutatedVar, aliases, liveAfter, candidates) !== "";
}
