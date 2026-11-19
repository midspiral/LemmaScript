import type { Expr } from "./ir.js";

/** Whether a record-valued initializer needs context for a fresh literal.
 *  Calls, projections, variables, and spread updates supply their own type;
 *  their arguments/fields receive context without annotating the binding.
 *  Lean can infer an `if` from either branch, but elaborates match arms in order. */
export function needsRecordType(e: Expr): boolean {
  return recordTypeSource(e) === "literal";
}

/** An absent optional has no payload type to contribute to another branch. */
function recordTypeSource(e: Expr): "value" | "literal" | "absent" {
  switch (e.kind) {
    case "record": return e.spread ? "value" : "literal";
    case "var": return e.name === "undefined" ? "absent" : "value";
    case "constructor":
      if (e.type !== "Option") return "value";
      return e.name === "none" ? "absent" : recordTypeSource(e.args[0]);
    case "if": {
      const branches = [recordTypeSource(e.then), recordTypeSource(e.else)];
      return branches.includes("value") ? "value" : branches.includes("literal") ? "literal" : "absent";
    }
    case "match": return e.arms.some(a => needsRecordType(a.body)) ? "literal" : "value";
    case "let": return recordTypeSource(e.body);
    default: return "value";
  }
}
