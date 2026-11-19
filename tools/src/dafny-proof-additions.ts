/**
 * Check the lines a `.dfy` proof adds to its `.dfy.gen` companion for
 * constructs that bypass verification.
 *
 * Added lines may not contain `assume` statements or `{:axiom}` / `@Axiom`
 * attributes. Text inside comments (including nested block comments),
 * strings (including verbatim strings), and character literals is ignored.
 * Separately, added lines may not introduce an `// lsc options:` header,
 * because verifier flags are read from that header in the proof.
 */

interface Token {
  text: string;
  line: number;
}

const OPERATORS = ["<==>", "==>", "<==", "==", "!=", "<=", ">=", ":=", "::", "->", "=>", "&&", "||", ".."];

function isWordStart(ch: string): boolean {
  return /[A-Za-z0-9_]/.test(ch);
}

function isWordChar(ch: string): boolean {
  return /[A-Za-z0-9_'?]/.test(ch);
}

/** Tokenize Dafny source, dropping comments and collapsing literals to single tokens. */
export function lexDafny(text: string): Token[] {
  const tokens: Token[] = [];
  let line = 0;
  let i = 0;
  const advance = (to: number) => {
    for (; i < to && i < text.length; i++) if (text[i] === "\n") line++;
  };
  while (i < text.length) {
    const ch = text[i];
    const next = text[i + 1];
    if (/\s/.test(ch)) { advance(i + 1); continue; }
    if (ch === "/" && next === "/") {
      const end = text.indexOf("\n", i);
      advance(end < 0 ? text.length : end);
      continue;
    }
    if (ch === "/" && next === "*") {
      let depth = 0;
      let j = i;
      while (j < text.length) {
        if (text[j] === "/" && text[j + 1] === "*") { depth++; j += 2; }
        else if (text[j] === "*" && text[j + 1] === "/") { depth--; j += 2; if (depth === 0) break; }
        else j++;
      }
      advance(j);
      continue;
    }
    const start = line;
    if (ch === "@" && next === "\"") {
      let j = i + 2;
      while (j < text.length) {
        if (text[j] === "\"" && text[j + 1] === "\"") j += 2;
        else if (text[j] === "\"") { j++; break; }
        else j++;
      }
      tokens.push({ text: "\"\"", line: start });
      advance(j);
      continue;
    }
    if (ch === "\"") {
      let j = i + 1;
      while (j < text.length && text[j] !== "\"" && text[j] !== "\n") j += text[j] === "\\" ? 2 : 1;
      tokens.push({ text: "\"\"", line: start });
      advance(j + 1);
      continue;
    }
    if (ch === "'") {
      const literal = /^'(?:\\u\{[0-9A-Fa-f_]+\}|\\U\{[0-9A-Fa-f_]+\}|\\u[0-9A-Fa-f]{4}|\\.|[^'\\\n])'/u.exec(text.slice(i));
      if (literal) {
        tokens.push({ text: "''", line: start });
        advance(i + literal[0].length);
        continue;
      }
    }
    if (isWordStart(ch)) {
      let j = i + 1;
      while (j < text.length && isWordChar(text[j])) j++;
      tokens.push({ text: text.slice(i, j), line: start });
      advance(j);
      continue;
    }
    if (ch === "{" && next === ":") {
      tokens.push({ text: "{:", line: start });
      advance(i + 2);
      continue;
    }
    const op = OPERATORS.find(o => text.startsWith(o, i));
    tokens.push({ text: op ?? ch, line: start });
    advance(i + (op?.length ?? 1));
  }
  return tokens;
}

/**
 * Mark the proof lines that are not generated lines, matching each generated
 * line to the earliest equal proof line. Returns undefined when the generated
 * lines do not all appear in order.
 */
function addedLines(genLines: string[], proofLines: string[]): boolean[] | undefined {
  const added: boolean[] = [];
  let g = 0;
  for (const line of proofLines) {
    const generated = g < genLines.length && line === genLines[g];
    if (generated) g++;
    added.push(!generated);
  }
  return g === genLines.length ? added : undefined;
}

/** Matches the header `dafnyVerifyArgs` reads verifier options from. */
const LSC_OPTIONS_HEADER = /^\/\/ lsc options:/;

/**
 * Check the proof additions, returning one diagnostic per rejected construct.
 * Diagnostics name the 1-based proof line, the reason, and the line text.
 */
export function proofAdditionViolations(generated: string, proof: string, proofName: string): string[] {
  const proofLines = proof.split("\n");
  const added = addedLines(generated.split("\n"), proofLines);
  if (!added) return [`${proofName}: generated lines are not contained in order in the proof`];

  const violations: string[] = [];
  const report = (line: number, reason: string) =>
    violations.push(`${proofName}:${line + 1}: ${reason}: ${proofLines[line].trim()}`);

  const tokens = lexDafny(proof);
  for (let k = 0; k < tokens.length; k++) {
    const t = tokens[k];
    if (!added[t.line]) continue;
    const following = tokens[k + 1]?.text;
    if (t.text === "assume") report(t.line, "assume statements are not allowed in proof additions; prove the fact instead");
    else if (t.text === "{:" && following === "axiom") report(t.line, "{:axiom} attributes are not allowed in proof additions; give the declaration a proof or body");
    else if (t.text === "@" && following === "Axiom") report(t.line, "@Axiom attributes are not allowed in proof additions; give the declaration a proof or body");
  }

  proofLines.forEach((text, line) => {
    if (added[line] && LSC_OPTIONS_HEADER.test(text)) {
      report(line, "an added `// lsc options:` line would change verifier options; options come from the generated file");
    }
  });
  return violations;
}
