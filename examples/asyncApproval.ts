/*
 * An approval gate in the shape of a sandbox-escalation check (SPEC §4.5).
 *
 * `throw` in an async function rejects the returned promise, so every denial
 * path owes nothing; `ensures` constrains only the granted mode. `askUser` is
 * external I/O: an impure extern, so each call may answer differently.
 *
 * The request is destructured before the first await. Reading `request`
 * itself after the await would be rejected: another task could modify the
 * object while this one waits for the user.
 */
//@ backend dafny

export type Mode = "read-only" | "workspace-write" | "full-access";
export type Outcome = "allowed-once" | "rejected" | "cancelled";

export interface Request {
  requested: Mode;
  effective: Mode;
  justification: string;
}

export function rank(m: Mode): number {
  //@ ensures 0 <= \result && \result <= 2
  return m === "read-only" ? 0 : m === "workspace-write" ? 1 : 2;
}

//@ extern
//@ impure
export async function askUser(reason: string): Promise<Outcome> {
  return "rejected";  // the real implementation prompts a human
}

export async function approve(request: Request): Promise<Mode> {
  //@ ensures \result === request.effective || rank(\result) > rank(request.effective)
  const { requested, effective, justification } = request;
  if (requested === effective) return effective;
  if (rank(requested) <= rank(effective)) {
    throw new Error("escalation must be strictly wider than the current mode");
  }
  if (justification === "") throw new Error("escalation requires a justification");
  const outcome = await askUser(justification);
  switch (outcome) {
    case "allowed-once":
      return requested;
    case "rejected":
      throw new Error("the user rejected the escalation");
    case "cancelled":
      throw new Error("the approval request was cancelled");
  }
}

export async function grantedRank(request: Request): Promise<number> {
  //@ ensures \result >= rank(request.effective)
  // A caller reasons against approve's contract; a rejection ends this path too.
  const granted = await approve(request);
  return rank(granted);
}
