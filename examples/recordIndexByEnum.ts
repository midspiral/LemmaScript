// Indexing a record by an enum (string-union) key — `rec[k]` where `k` ranges
// over field names. Resolve lowers it so the dynamic field access verifies like
// a static one: a *named* key is a datatype, so it becomes `match k { case f =>
// rec.f }`; an *inline* key (`"a" | "b"`) is a bare string, so it becomes an
// equality chain `if k === "a" then rec.a else …`. Either way it covers exactly
// the key's members, so a key that is a subset of the fields stays sound.

type Level = "low" | "medium" | "high";

interface Budgets {
	low: number;
	medium: number;
	high: number;
}

// Named key → match. Result is one of the indexed fields.
//@ verify
//@ ensures \result === b.low || \result === b.medium || \result === b.high
export function budgetFor(b: Budgets, level: Level): number {
	return b[level];
}

interface OptBudgets {
	low?: number;
	high?: number;
}

// Inline key + optional fields → equality chain; the access keeps the `Option` type.
//@ verify
//@ ensures \result === b.low || \result === b.high
export function maybeBudget(b: OptBudgets, level: "low" | "high"): number | undefined {
	return b[level];
}

// Inline key that is a subset of the record's fields — the chain covers just the
// key's members (a stray `high` branch would be unsound, so it isn't emitted).
//@ verify
//@ ensures \result === b.low || \result === b.medium
export function lowOrMid(b: Budgets, level: "low" | "medium"): number {
	return b[level];
}
