/*
 * Top-level inline closures — an Express-style handler defined directly in the
 * route registration, app.get("/x", (req, res) => { ... }), rather than hoisted
 * into a named const. LemmaScript "moves" such a closure to the top level: it is
 * extracted as a synthetic function (named from the call's method and route, so
 * the handler below becomes get_entries) and honors its own //@ verify and
 * //@ autohavoc annotations.
 *
 * The handler is fully idiomatic Express: `async (req, res)`. `res` no longer
 * collides with Dafny's `res` out-parameter (the emitter picks a fresh name),
 * and the `async` Promise<T> return wrapper is unwrapped to T — sound here
 * because the body has no `await` (no suspension point to model).
 *
 * As in autohavoc.ts, the opaque request I/O is havoc'd and the only obligation
 * left is that the safePath guard dominates the readSafe sink.
 */
//@ backend dafny

function safePath(path: string): boolean {
  //@ verify
  return !path.includes("..");
}

//@ extern
//@ requires safePath(path)
function readSafe(path: string): string {
  return "";  // real impl reads the filesystem; body skipped by the extern annotation
}

const app: any = {};

app.get("/entries", async (req: any, res: any) => {
  //@ verify
  //@ autohavoc
  const id: string = req.query.id;       // opaque → arbitrary string
  const filePath = "./entries/" + id + ".json";

  if (!safePath(filePath)) {
    return res.status(400).send("invalid id");
  }

  const contents = readSafe(filePath);   // requires safePath(filePath) — discharged by the guard above
  return res.status(200).send(contents);
});
