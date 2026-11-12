export function cutoff(t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures t <= 0 ==> \result === 0
  //@ ensures t > 0 ==> \result === t
  if (t <= 0) return 0;
  return t;
}

export function direction(t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures t < 0 ==> \result === -1
  //@ ensures t >= 0 ==> \result === 1
  return t < 0 ? -1 : 1;
}

export function half(t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures \result * 2 === t
  return t / 2;
}

export function halfOfOne(): number {
  //@ verify
  //@ type \result real
  //@ ensures \result === 0.5
  return half(1);
}

export function negative(): number {
  //@ verify
  //@ type \result real
  //@ ensures \result === -2
  return -(2);
}

export function chosenHalf(flag: boolean): number {
  //@ verify
  //@ type \result real
  //@ ensures flag ==> \result === -0.5
  //@ ensures !flag ==> \result === 0.5
  return half(flag ? -1 : 1);
}

export function nestedChoice(first: boolean, second: boolean): number {
  //@ verify
  //@ type \result real
  //@ ensures \result === (first ? (second ? -1 : 0) : 1)
  return first ? (second ? -1 : 0) : 1;
}

export function localReal(flag: boolean): number {
  //@ verify
  //@ type value real
  //@ type \result real
  //@ ensures flag ==> \result === -1
  //@ ensures !flag ==> \result === 0
  let value = 0;
  if (flag) value = -1;
  return value;
}

export function maybeZero(flag: boolean): number | undefined {
  //@ verify
  //@ type \result real|undefined
  //@ ensures flag ==> \result !== undefined
  //@ ensures !flag ==> \result === undefined
  //@ ensures \result !== undefined ==> \result === 0
  return flag ? 0 : undefined;
}

export function maybeNegative(flag: boolean): number | undefined {
  //@ verify
  //@ type \result real|undefined
  //@ ensures flag ==> \result === undefined
  //@ ensures !flag ==> \result !== undefined
  //@ ensures \result !== undefined ==> \result === -1
  return flag ? undefined : -1;
}

export function withDefault(t?: number): number {
  //@ verify
  //@ type t real|undefined
  //@ type \result real
  //@ ensures t === undefined ==> \result === 0
  //@ ensures t !== undefined ==> \result === t
  return t ?? 0;
}

export function optionalArgument(flag: boolean): number {
  //@ verify
  //@ type \result real
  //@ ensures flag ==> \result === 1
  //@ ensures !flag ==> \result === 0
  return withDefault(flag ? 1 : undefined);
}

export function presentArgument(): number {
  //@ verify
  //@ type \result real
  //@ ensures \result === -1
  return withDefault(-1);
}

export function literalVector(): number[] {
  //@ verify
  //@ type \result real[]
  //@ ensures \result.length === 2 && \result[0] === 0 && \result[1] === -1
  return [0, -1];
}
