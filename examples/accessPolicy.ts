//@ backend dafny,fstar

// Compose reusable access rules. Predicates are pure and total.
export interface Predicate<A> {
  (value: A): boolean;
}

export function either<A>(first: Predicate<A>, second: Predicate<A>): Predicate<A> {
  //@ ensures forall(value: A, \result(value) === (first(value) || second(value)))
  return value => first(value) || second(value);
}

export function denyOverride<A>(eligible: Predicate<A>, denied: Predicate<A>): Predicate<A> {
  //@ ensures forall(value: A, \result(value) === (eligible(value) && !denied(value)))
  return value => eligible(value) && !denied(value);
}

export function accessPolicy<A>(
  primary: Predicate<A>,
  fallback: Predicate<A>,
  denied: Predicate<A>,
): Predicate<A> {
  //@ ensures forall(value: A, \result(value) === ((primary(value) || fallback(value)) && !denied(value)))
  const eligible = either(primary, fallback);
  return denyOverride(eligible, denied);
}

export interface AccessRequest {
  member: boolean;
  invited: boolean;
  suspended: boolean;
}

// Members and invited guests may enter unless their account is suspended.
export function canEnter(request: AccessRequest): boolean {
  //@ ensures \result === ((request.member || request.invited) && !request.suspended)
  return accessPolicy(
    (candidate: AccessRequest): boolean => candidate.member,
    (candidate: AccessRequest): boolean => candidate.invited,
    (candidate: AccessRequest): boolean => candidate.suspended,
  )(request);
}

export function suspendedCannotEnter(request: AccessRequest): boolean {
  //@ requires request.suspended
  //@ ensures !\result
  return canEnter(request);
}
