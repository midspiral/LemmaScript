/**
 * Check the lines a `.dfy` proof adds to its `.dfy.gen` companion for
 * constructs that bypass verification or weaken generated contracts.
 *
 * Added lines may not contain `assume`, `expect`, `decreases *`, `{:axiom}`,
 * `@Axiom`, `{:verify false}`, `{:only}`, `@VerifyOnly`, or `{:extern}`.
 * Text inside comments (including nested block comments), strings (including
 * verbatim strings), and character literals is ignored.
 *
 * Inside a generated declaration header (before its body `{` or the next
 * declaration for bodyless declarations), added lines may introduce complete
 * `ensures`, `modifies`, `reads`, or `decreases` clauses (other than
 * `decreases *`), but may not add `requires` clauses or extend/split a
 * generated signature or header clause. Auxiliary declarations added in the
 * proof may declare their own `requires` and other clauses freely.
 *
 * Separately, added lines may not introduce an `// lsc options:` header,
 * because verifier flags are read from that header in the proof, and may not
 * contain line breaks other than `\n` (Dafny ends a `//` comment at `\r`).
 * A generated line kept in the proof must lex to the same tokens it has in
 * the generated file, so added comments or strings cannot disable it, and an
 * added line may not repeat a generated verification-bypass line.
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

/** Whether a token sequence bypasses verification or assumes an unproved fact. */
function trustsFact(tokens: Token[], k: number): { reason: string; end: number } | undefined {
  const t = tokens[k].text, following = tokens[k + 1]?.text;
  if (t === "assume") return { reason: "assume statements are not allowed in proof additions; prove the fact instead", end: k };
  if (t === "expect") return { reason: "expect statements are not allowed in proof additions; prove the fact instead", end: k };
  if (t === "decreases" && following === "*")
    return { reason: "`decreases *` is not allowed in proof additions; provide a termination metric instead", end: k + 1 };
  if (t === "{:" && following === "axiom")
    return { reason: "{:axiom} attributes are not allowed in proof additions; give the declaration a proof or body", end: k + 1 };
  if (t === "@" && following === "Axiom")
    return { reason: "@Axiom attributes are not allowed in proof additions; give the declaration a proof or body", end: k + 1 };
  if (t === "{:" && following === "verify" && !(tokens[k + 2]?.text === "true" && tokens[k + 3]?.text === "}")) {
    const close = findMatchingBrace(tokens, k);
    return {
      reason: "{:verify ...} attributes that disable verification are not allowed in proof additions",
      end: close >= 0 ? close : k + 1,
    };
  }
  if (t === "{:" && following === "only")
    return { reason: "{:only} attributes are not allowed in proof additions; they skip verification of other declarations", end: k + 1 };
  if (t === "@" && following === "VerifyOnly")
    return { reason: "@VerifyOnly attributes are not allowed in proof additions; they skip verification of other declarations", end: k + 1 };
  if (t === "{:" && following === "extern")
    return { reason: "{:extern} attributes are not allowed in proof additions; declare externs in TypeScript with //@ extern", end: k + 1 };
  return undefined;
}

const CALLABLE_KEYWORDS = new Set(["method", "lemma", "function", "predicate", "constructor"]);
const DECL_MODIFIERS = new Set(["ghost", "twostate", "least", "greatest", "static", "opaque", "protected", "abstract"]);
const CONTAINER_KEYWORDS = new Set(["class", "trait", "module"]);
const NON_CALLABLE_DECLS = new Set([
  "datatype", "codatatype", "type", "newtype", "class", "trait", "module",
  "const", "import", "include", "export",
]);
const SPEC_CLAUSE_KEYWORDS = new Set(["requires", "ensures", "reads", "modifies", "decreases"]);
const ALLOWED_ADDED_HEADER_CLAUSES = new Set(["ensures", "reads", "modifies", "decreases"]);

/** Whether `tokens[k]` is a modifier prefixing a declaration (not an identifier like `least` in an expression). */
function isDeclModifierAt(tokens: Token[], k: number): boolean {
  let i = k;
  while (i < tokens.length && DECL_MODIFIERS.has(tokens[i].text)) i++;
  if (i === k || i >= tokens.length) return false;
  const next = tokens[i].text;
  return CALLABLE_KEYWORDS.has(next) || NON_CALLABLE_DECLS.has(next) || next === "var";
}

/** Tokens after a closing `}` that show `{ ... }` was a set literal inside a header, not a body. */
const HEADER_CONTINUATION_AFTER_BRACE = new Set([
  "requires", "ensures", "reads", "modifies", "decreases", "{",
  "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "%",
  "&&", "||", "==>", "<==", "<==>", "in", "!", ".", "[", "(", ")", "]", ",", "?", ":", "::", "|", ";",
  "then", "else", "as", "is",
]);

/** Tokens before `{` inside a spec clause that unambiguously introduce a set/multiset literal. */
const EXPR_BEFORE_BRACE = new Set([
  "requires", "ensures", "reads", "modifies", "decreases",
  "==", "!=", "<=", ">=", "<", "+", "-", "*", "/", "%",
  "&&", "||", "==>", "<==", "<==>", "!", "in", "::", "|", ":=",
  "then", "else", "iset", "multiset", "set",
]);

/** Return the index of the `}` matching `tokens[openIdx]` (`{` or `{:`), or -1. */
function findMatchingBrace(tokens: Token[], openIdx: number): number {
  let depth = 0;
  for (let i = openIdx; i < tokens.length; i++) {
    const text = tokens[i].text;
    if (text === "{" || text === "{:") depth++;
    else if (text === "}") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

/** Whether `{` at `openIdx` inside a declaration header is a set/multiset literal rather than the body `{`. */
function isHeaderExprBrace(tokens: Token[], openIdx: number, inSpecClause: boolean): boolean {
  const closeIdx = findMatchingBrace(tokens, openIdx);
  const afterClose = closeIdx >= 0 ? tokens[closeIdx + 1]?.text : undefined;
  if (afterClose !== undefined && HEADER_CONTINUATION_AFTER_BRACE.has(afterClose)) return true;
  const prev = openIdx > 0 ? tokens[openIdx - 1]?.text : undefined;
  if (inSpecClause && prev !== undefined && EXPR_BEFORE_BRACE.has(prev)) return true;
  return false;
}

type BraceKind = "container" | "body" | "attr" | "expr";

/**
 * Check generated callable declaration headers for added `requires` clauses,
 * added continuations that alter a generated signature or clause, and added
 * clauses that split a multi-line generated clause.
 */
function checkGeneratedHeaders(
  tokens: Token[],
  added: boolean[],
  report: (line: number, reason: string) => void,
): void {
  let parenDepth = 0;
  let bracketDepth = 0;
  const braceStack: BraceKind[] = [];

  let pendingContainer = false;
  let inGenHeader = false;
  let inAddedHeader = false;
  let headerSawCallable = false;
  let headerHasName = false;
  let inSpecClause = false;
  let inAddedClause = false;
  let declContainerDepth = 0;
  const reportedExtendLines = new Set<number>();

  const resetHeader = () => {
    inGenHeader = false;
    inAddedHeader = false;
    headerSawCallable = false;
    headerHasName = false;
    inSpecClause = false;
    inAddedClause = false;
  };

  for (let k = 0; k < tokens.length; k++) {
    const t = tokens[k];
    const text = t.text;
    const isAdded = added[t.line];
    const prev = k > 0 ? tokens[k - 1].text : undefined;

    if (text === "{:") {
      braceStack.push("attr");
      continue;
    }

    if (text === "{") {
      const inNonContainer = braceStack.some(b => b !== "container");
      if (parenDepth > 0 || bracketDepth > 0 || inNonContainer) {
        braceStack.push("expr");
      } else if (pendingContainer) {
        pendingContainer = false;
        resetHeader();
        braceStack.push("container");
      } else if ((inGenHeader || inAddedHeader) && isHeaderExprBrace(tokens, k, inSpecClause)) {
        if (inGenHeader && isAdded && !inAddedClause && !reportedExtendLines.has(t.line)) {
          reportedExtendLines.add(t.line);
          report(t.line, "added lines in a generated declaration header must start a new ensures, modifies, reads, or decreases clause and may not extend a generated signature or clause");
        }
        braceStack.push("expr");
      } else {
        resetHeader();
        braceStack.push("body");
      }
      continue;
    }

    if (text === "}") {
      braceStack.pop();
      continue;
    }

    const inNonContainer = braceStack.some(b => b !== "container");
    const atDeclLevel = parenDepth === 0 && bracketDepth === 0 && !inNonContainer;

    if (text === "(") {
      if (inGenHeader && isAdded && !inAddedClause && !reportedExtendLines.has(t.line)) {
        reportedExtendLines.add(t.line);
        report(t.line, "added lines in a generated declaration header must start a new ensures, modifies, reads, or decreases clause and may not extend a generated signature or clause");
      }
      parenDepth++;
      continue;
    }
    if (text === ")") {
      if (parenDepth > 0) parenDepth--;
      if (inGenHeader && isAdded && !inAddedClause && !reportedExtendLines.has(t.line)) {
        reportedExtendLines.add(t.line);
        report(t.line, "added lines in a generated declaration header must start a new ensures, modifies, reads, or decreases clause and may not extend a generated signature or clause");
      }
      continue;
    }
    if (text === "[") {
      if (inGenHeader && isAdded && !inAddedClause && !reportedExtendLines.has(t.line)) {
        reportedExtendLines.add(t.line);
        report(t.line, "added lines in a generated declaration header must start a new ensures, modifies, reads, or decreases clause and may not extend a generated signature or clause");
      }
      bracketDepth++;
      continue;
    }
    if (text === "]") {
      if (bracketDepth > 0) bracketDepth--;
      if (inGenHeader && isAdded && !inAddedClause && !reportedExtendLines.has(t.line)) {
        reportedExtendLines.add(t.line);
        report(t.line, "added lines in a generated declaration header must start a new ensures, modifies, reads, or decreases clause and may not extend a generated signature or clause");
      }
      continue;
    }

    if (atDeclLevel && prev !== ".") {
      // `by method {` follows a function body and is not a new method declaration.
      if (text === "method" && prev === "by") continue;

      if (NON_CALLABLE_DECLS.has(text)) {
        resetHeader();
        pendingContainer = CONTAINER_KEYWORDS.has(text);
        continue;
      }

      if (text === "var" && !headerSawCallable) {
        resetHeader();
        pendingContainer = false;
        continue;
      }

      if (CALLABLE_KEYWORDS.has(text) || isDeclModifierAt(tokens, k)) {
        pendingContainer = false;
        if ((!inGenHeader && !inAddedHeader) || headerHasName) {
          inGenHeader = !isAdded;
          inAddedHeader = isAdded;
          headerSawCallable = CALLABLE_KEYWORDS.has(text);
          headerHasName = false;
          inSpecClause = false;
          inAddedClause = false;
          declContainerDepth = braceStack.length;
        } else {
          if (CALLABLE_KEYWORDS.has(text)) headerSawCallable = true;
          if (!isAdded) {
            inGenHeader = true;
            inAddedHeader = false;
          }
        }
        continue;
      }

      if ((inGenHeader || inAddedHeader) && headerSawCallable && !headerHasName) {
        headerHasName = true;
        if (!inGenHeader) continue;
      }
    }

    if (!inGenHeader) continue;

    const atHeaderClauseLevel = parenDepth === 0 && bracketDepth === 0 && braceStack.length === declContainerDepth;

    if (!isAdded) {
      if (atHeaderClauseLevel) {
        if (SPEC_CLAUSE_KEYWORDS.has(text)) {
          inSpecClause = true;
          inAddedClause = false;
        } else if (inAddedClause) {
          report(t.line, "an added clause splits a generated header clause");
          inAddedClause = false;
        }
      }
      continue;
    }

    // Token is on an added line inside a generated declaration header.
    if (atHeaderClauseLevel) {
      if (text === "requires") {
        report(t.line, "added requires clauses are not allowed in generated declaration headers; strengthen preconditions in TypeScript instead");
        inSpecClause = true;
        // Suppress follow-on continuation diagnostics for the body of this rejected clause.
        inAddedClause = true;
      } else if (ALLOWED_ADDED_HEADER_CLAUSES.has(text)) {
        inSpecClause = true;
        inAddedClause = true;
      } else if (!inAddedClause && !reportedExtendLines.has(t.line)) {
        reportedExtendLines.add(t.line);
        report(t.line, "added lines in a generated declaration header must start a new ensures, modifies, reads, or decreases clause and may not extend a generated signature or clause");
      }
    } else if (!inAddedClause && !reportedExtendLines.has(t.line)) {
      reportedExtendLines.add(t.line);
      report(t.line, "added lines in a generated declaration header must start a new ensures, modifies, reads, or decreases clause and may not extend a generated signature or clause");
    }
  }
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
    const match = trustsFact(tokens, k);
    if (!match) continue;
    let addedLine = -1;
    for (let j = k; j <= match.end && j < tokens.length; j++) {
      if (added[tokens[j].line]) { addedLine = tokens[j].line; break; }
    }
    if (addedLine >= 0) report(addedLine, match.reason);
  }
  checkGeneratedHeaders(tokens, added, report);

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
      report(line, "added lines may not repeat a generated assume, axiom, or verification-bypass line; keep the generated line in place");
  });
  return violations;
}
