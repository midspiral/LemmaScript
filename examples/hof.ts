/**
 * Higher-order function examples.
 */

export function doubleAll(arr: number[]): number[] {
  //@ ensures $result.length === arr.length
  return arr.map((x) => x * 2);
}

export function positives(arr: number[]): number[] {
  return arr.filter((x) => x > 0);
}

export function allPositive(arr: number[]): boolean {
  return arr.every((x) => x > 0);
}

export function hasNegative(arr: number[]): boolean {
  return arr.some((x) => x < 0);
}

interface QuoteElement {
  QuoteId: string;
  ConditionallyHidden?: boolean;
}

interface QuoteElements {
  Elements: QuoteElement[];
}

// A record-typed callback keeps one parameter while destructuring its fields.
//@ ensures $result.length <= comparisonElements.Elements.length
//@ ensures forall(e => implies(e in $result, e.QuoteId === quoteId && !e.ConditionallyHidden))
export function visibleElementsForQuote(comparisonElements: QuoteElements, quoteId: string): QuoteElement[] {
  return comparisonElements.Elements.filter(
    ({ QuoteId, ConditionallyHidden }) => QuoteId === quoteId && !ConditionallyHidden
  );
}
