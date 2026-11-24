interface Content { values: number | number[] }

export function optionalUnion(box: Content | undefined): number {
  //@ ensures box === undefined ==> \result === 0
  if (box !== undefined && Array.isArray(box.values)) return box.values.length;
  return 0;
}

export function optionalUnionTernary(box: Content | undefined): number {
  //@ ensures box === undefined ==> \result === 0
  return box !== undefined && Array.isArray(box.values) ? box.values.length : 0;
}
