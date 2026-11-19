export type Phase = "pending" | "executing" | "complete";

export interface Snapshot {
  current: Phase;
  previous: Phase | null;
  scheduled: Phase | undefined;
  hint?: Phase;
  fallback: Phase | null | undefined;
  retryHint?: Phase | null;
  timeline: Phase[];
}

export function isExecuting(p: Phase): boolean {
  //@ verify
  return p === "executing";
}

export function previouslyExecuting(s: Snapshot): boolean {
  //@ verify
  //@ ensures s.previous !== null ==> \result === isExecuting(s.previous)
  if (s.previous === null) return false;
  return isExecuting(s.previous);
}

export function priorPhaseIsKnown(s: Snapshot): boolean {
  //@ verify
  //@ ensures \result
  if (s.previous === null) return true;
  if (s.previous === "pending") return true;
  return s.previous === "executing" || s.previous === "complete";
}
