type Z = 0 | 1 | 2;

//@ verify
//@ ensures \result === 5
export function zTruth(z: Z): number { return z ? 5 : 6; }

//@ verify
//@ ensures \result === false
export function zNot(z: Z): boolean { return !z; }
