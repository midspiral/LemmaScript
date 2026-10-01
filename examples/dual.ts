//@ backend dafny,fstar

// Typed data-last currying: dual(body)(that)(self) equals body(self, that).
// This step models pure, total callbacks. Effect's argument-count dispatch
// and overloaded dual(2, body) API remain outside this example.
export function dual<A, B, R>(body: (self: A, that: B) => R): (that: B) => (self: A) => R {
  //@ ensures forall(that: B, forall(self: A, \result(that)(self) === body(self, that)))
  return (that: B): ((self: A) => R) => (self: A): R => body(self, that);
}

export type Predicate<A> = (value: A) => boolean;

export function denyOverride<A>(self: Predicate<A>, denied: Predicate<A>): Predicate<A> {
  //@ ensures forall(value: A, \result(value) === (self(value) && !denied(value)))
  return value => self(value) && !denied(value);
}

export function mapInput<A, B>(self: Predicate<A>, project: (value: B) => A): Predicate<B> {
  //@ ensures forall(value: B, \result(value) === self(project(value)))
  return value => self(project(value));
}

// Keep and compose partial applications, mapping B inputs to A policy values.
export function curriedPolicy<A, B>(
  eligible: Predicate<A>, denied: Predicate<A>, project: (value: B) => A,
): Predicate<B> {
  //@ ensures forall(value: B, \result(value) === (eligible(project(value)) && !denied(project(value))))
  const denyLast = dual((self: Predicate<A>, denied: Predicate<A>): Predicate<A> => denyOverride(self, denied));
  const mapLast = dual((self: Predicate<A>, project: (value: B) => A): Predicate<B> => mapInput(self, project));
  const withDenial = denyLast(denied);
  const onInput = mapLast(project);
  return onInput(withDenial(eligible));
}

export function callingFormsAgree<A, B>(
  eligible: Predicate<A>, denied: Predicate<A>, project: (value: B) => A, value: B,
): boolean {
  //@ ensures \result
  const direct = mapInput(denyOverride(eligible, denied), project);
  const curried = curriedPolicy(eligible, denied, project);
  return direct(value) === curried(value);
}

export interface Account {
  member: boolean;
  suspended: boolean;
}
export interface Request {
  account: Account;
}

// Map a request to its account, then enforce denial even for eligible members.
export function canEnter(request: Request): boolean {
  //@ ensures \result === (request.account.member && !request.account.suspended)
  return curriedPolicy(
    (account: Account): boolean => account.member,
    (account: Account): boolean => account.suspended,
    (request: Request): Account => request.account,
  )(request);
}
