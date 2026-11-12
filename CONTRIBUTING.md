# Contributing to LemmaScript

## Development Rules

### Let the backend (e.g., Dafny) do the checking

- Resolve the information needed to choose a translation.
- Avoid duplicating backend checks.

### Make special cases compose

- When a rule does not apply, let ordinary lowering continue.
- A mistranslation or dropped contract can still verify; check what later passes will do with the fallthrough.
- Before adding a `throw`, identify the incorrect translation it prevents.

### Keep generated output stable

- Handwritten proofs depend on its names and structure.
- Avoid incidental changes to generated output.

### Add end-to-end verification examples

- If the change makes a new example verifiable, add it to `examples/`.
