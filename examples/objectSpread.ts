/**
 * Object-literal properties fold in source order: a spread overrides earlier
 * properties. `{ id: 0, ...u }` is `u` (u's id wins); `{ ...u, id: v }` sets id.
 */

interface User { id: number; name: number }

export function withSpreadLast(u: User): User {
  //@ ensures \result === u
  return { id: 0, ...u };
}

export function withFieldLast(u: User, v: number): User {
  //@ ensures \result.id === v
  return { ...u, id: v };
}
