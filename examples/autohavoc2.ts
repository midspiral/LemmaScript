/*
 * autohavoc, continued — a contracted call's precondition is still checked even
 * when the call is buried inside an expression that gets havoc'd.
 *
 * In mergeEntries the filesystem reads (readFileSafe) sit *inside* an opaque
 * JSON.parse / string concat that autohavoc blanks out. Naively havocing the
 * whole expression would discard the readFileSafe calls along with their
 * requires obligations — a silent false pass. Instead the pass hoists each
 * contracted call to its own checked statement (var _ := readFileSafe(...))
 * before havocing the result, so both validPath preconditions are discharged
 * by the guards. Hoisting is transitive: a contracted call nested at any depth
 * (here, inside a `+` inside JSON.parse) is found and preserved.
 *
 * This file is also a golden-file regression test for that behavior — the
 * generated .dfy.gen shows the hoisted readFileSafe statements.
 */
//@ backend dafny

function validPath(path: string): boolean {
  //@ verify
  return !path.includes("..");
}

//@ extern
//@ requires validPath(path)
function readFileSafe(path: string): string {
  return "";  // real impl reads the filesystem; body skipped by the extern annotation
}

function mergeEntries(req: any): string {
  //@ verify
  //@ autohavoc
  const a: string = req.query.a;
  const b: string = req.query.b;
  const pa = "./data/" + a + ".json";
  const pb = "./data/" + b + ".json";

  if (!validPath(pa)) {
    return "invalid a";
  }
  if (!validPath(pb)) {
    return "invalid b";
  }

  // Both reads are nested inside an unmodellable JSON.parse(...); the pass
  // hoists each to a checked statement so neither precondition is lost.
  const merged: string = JSON.parse(readFileSafe(pa) + readFileSafe(pb));
  return merged;
}
