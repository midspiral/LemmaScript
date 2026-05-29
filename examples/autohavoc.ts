/*
 * The `autohavoc` annotation abstracts every expression LemmaScript can't model
 * to a nondeterministic value, so verification rests only on the declared
 * contracts. It is the complement of the `extern` annotation: extern declares a
 * trusted boundary you reason against; autohavoc blanks the surrounding code you
 * do not want to model at all.
 *
 * loadEntry is a miniature request handler — it mixes opaque I/O (a typed-any
 * request object, JSON parsing) with a filesystem sink guarded against path
 * traversal. The opaque parts (req.query.id, JSON.parse) have no Dafny model;
 * without the annotation they would make the function unemittable. With it, they
 * become arbitrary values and the only obligation left is that the validPath
 * guard dominates readFileSafe — discharging its precondition.
 *
 * Soundness: havoc is a nondeterministic over-approximation (assume nothing), so
 * this can only make a proof fail, never spuriously pass. The trust boundary is
 * the declared sink: a real filesystem call must go through readFileSafe.
 */
//@ backend dafny

function validPath(path: string): boolean {
  //@ verify
  return !path.includes("..");
}

//@ extern
//@ requires validPath(path)
function readFileSafe(path: string): string {
  return "";  // real impl reads the filesystem; body skipped by //@ extern
}

interface Entry {
  id: string;
  name: string;
}

function loadEntry(req: any): string {
  //@ verify
  //@ autohavoc
  const id: string = req.query.id;       // opaque → arbitrary string
  const filePath = "./data/" + id + ".json";

  if (!validPath(filePath)) {
    return "invalid path";
  }

  const raw = readFileSafe(filePath);    // requires validPath(filePath) — discharged by the guard above
  const entry: Entry = JSON.parse(raw);  // opaque → arbitrary Entry
  return entry.name;                     // a typed field of a havoc'd value is still modellable
}
