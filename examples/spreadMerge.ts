// Faithful object-spread merge `{ ...a, ...b }`. Later sources override earlier
// ones field by field, so a base default survives exactly when the override
// omits that field. Resolve expands the merge against the result type's fields
// (an optional field's presence decides at runtime).

export interface Budgets {
	low: number;
	high: number;
}

// Complete override: both required fields come from `over`.
//@ verify
//@ ensures \result.low === over.low
//@ ensures \result.high === over.high
export function mergeComplete(base: Budgets, over: Budgets): Budgets {
	return { ...base, ...over };
}

export interface Config {
	retries?: number;
	timeout?: number;
}

// Partial override: each default survives iff `over` omits that key — the
// property the old "keep only the last spread" lowering silently broke.
//@ verify
//@ ensures over.retries === undefined ==> \result.retries === base.retries
//@ ensures over.retries !== undefined ==> \result.retries === over.retries
//@ ensures over.timeout === undefined ==> \result.timeout === base.timeout
//@ ensures over.timeout !== undefined ==> \result.timeout === over.timeout
export function withDefaults(base: Config, over: Config): Config {
	return { ...base, ...over };
}

// Optional override operand: `undefined` spreads nothing, so the base shows through.
//@ verify
//@ ensures over === undefined ==> \result === base
//@ ensures over !== undefined ==> \result === over
export function applyOverride(base: Budgets, over?: Budgets): Budgets {
	return { ...base, ...over };
}

// Chain of spreads: the rightmost source wins.
//@ verify
//@ ensures \result.low === c.low && \result.high === c.high
export function mergeChain(a: Budgets, b: Budgets, c: Budgets): Budgets {
	return { ...a, ...b, ...c };
}
