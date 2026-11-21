/**
 * Check the lines a `.dfy` proof adds to its `.dfy.gen` companion for
 * constructs that bypass verification.
 *
 * Added lines may not contain `assume` statements or `{:axiom}` / `@Axiom`
 * attributes. Text inside comments (including nested block comments),
 * strings (including verbatim strings), and character literals is ignored.
 * Separately, added lines may not introduce an `// lsc options:` header,
 * because verifier flags are read from that header in the proof, and may not
 * contain line breaks other than `\n` (Dafny ends a `//` comment at `\r`).
 * A generated line kept in the proof must lex to the same tokens it has in
 * the generated file, so added comments or strings cannot disable it, and an
 * added line may not repeat a generated `assume` / axiom line.
 */

interface Token {
  text: string;
  line: number;
}

const OPERATORS = ["<==>", "==>", "<==", "==", "!=", "<=", ">=", ":=", "::", "->", "=>", "&&", "||", ".."];

/** Dafny identifiers may start with `'` or `?` (`?x` and `'x` are names). */
function isWordStart(ch: string): boolean {
  return /[A-Za-z0-9_'?]/.test(ch);
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
 * Map each proof line to the generated line it keeps, or -1 for an added
 * line, matching each generated line to the earliest equal proof line.
 * Returns undefined when the generated lines do not all appear in order.
 */
function matchGeneratedLines(genLines: string[], proofLines: string[]): number[] | undefined {
  const matched: number[] = [];
  let g = 0;
  for (const line of proofLines) {
    const generated = g < genLines.length && line === genLines[g];
    matched.push(generated ? g++ : -1);
  }
  return g === genLines.length ? matched : undefined;
}

/** Token texts starting on each line, joined with a separator. */
function tokensByLine(tokens: Token[], lineCount: number): string[] {
  const lines: string[][] = Array.from({ length: lineCount }, () => []);
  for (const t of tokens) lines[t.line]?.push(t.text);
  return lines.map(l => l.join("\u0000"));
}

/** Whether a token sequence contains an `assume`, `{:axiom}` or `@Axiom`. */
function trustsFact(tokens: Token[], k: number): string | undefined {
  const t = tokens[k].text, following = tokens[k + 1]?.text;
  if (t === "assume") return "assume statements are not allowed in proof additions; prove the fact instead";
  if (t === "{:" && following === "axiom") return "{:axiom} attributes are not allowed in proof additions; give the declaration a proof or body";
  if (t === "@" && following === "Axiom") return "@Axiom attributes are not allowed in proof additions; give the declaration a proof or body";
  return undefined;
}

/** Matches the header `dafnyVerifyArgs` reads verifier options from. */
const LSC_OPTIONS_HEADER = /^\/\/ lsc options:/m;

/** Line terminators other than `\n` that Dafny or a header regex may honor. */
const OTHER_LINE_BREAK = /[\r\u2028\u2029]/;

/**
 * Check the proof additions, returning one diagnostic per rejected construct.
 * Diagnostics name the 1-based proof line, the reason, and the line text.
 */
export function proofAdditionViolations(generated: string, proof: string, proofName: string): string[] {
  const proofLines = proof.split("\n");
  const genLines = generated.split("\n");
  const matched = matchGeneratedLines(genLines, proofLines);
  if (!matched) return [`${proofName}: generated lines are not contained in order in the proof`];
  const added = matched.map(g => g < 0);

  const violations: string[] = [];
  const report = (line: number, reason: string) =>
    violations.push(`${proofName}:${line + 1}: ${reason}: ${proofLines[line].trim()}`);

  const tokens = lexDafny(proof);
  for (let k = 0; k < tokens.length; k++) {
    if (!added[tokens[k].line]) continue;
    const reason = trustsFact(tokens, k);
    if (reason) report(tokens[k].line, reason);
  }

  const genTokens = lexDafny(generated);
  const trustedGenLines = new Set<string>();
  for (let k = 0; k < genTokens.length; k++) {
    if (trustsFact(genTokens, k)) trustedGenLines.add(genLines[genTokens[k].line]);
  }
  const proofLineTokens = tokensByLine(tokens, proofLines.length);
  const genLineTokens = tokensByLine(genTokens, genLines.length);

  proofLines.forEach((text, line) => {
    const g = matched[line];
    if (g >= 0) {
      if (proofLineTokens[line] !== genLineTokens[g])
        report(line, "added text changes how this generated line is read (for example, by placing it inside a comment or string)");
      return;
    }
    if (OTHER_LINE_BREAK.test(text))
      report(line, "added lines may only use `\\n` line breaks; Dafny ends a `//` comment at `\\r`");
    if (LSC_OPTIONS_HEADER.test(text))
      report(line, "an added `// lsc options:` line would change verifier options; options come from the generated file");
    if (trustedGenLines.has(text))
      report(line, "added lines may not repeat a generated assume or axiom line; keep the generated line in place");
  });
  return violations;
}
