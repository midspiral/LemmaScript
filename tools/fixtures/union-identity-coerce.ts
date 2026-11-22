export interface Claims { readonly aud: string | readonly string[] }

export function audiences(aud: string | readonly string[]): string[] {
  //@ verify
  if (Array.isArray(aud)) return [...aud]
  return [`${aud}`]
}

export function audienceCount(c: Claims): number {
  //@ verify
  return audiences(c.aud).length
}
