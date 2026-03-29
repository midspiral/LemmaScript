/**
 * LemmaScript //@ annotation extractor — Phase 0 prototype
 *
 * Parses a TypeScript file using ts-morph, extracts //@ annotations,
 * associates them with their AST nodes (functions, loops), and outputs
 * a structured IR that the code generator would consume.
 *
 * Usage: npx tsx src/extract.ts <file.ts>
 */

import { Project, SyntaxKind, Node, FunctionDeclaration, WhileStatement, ForStatement, SourceFile } from "ts-morph";

// ------------------------------------------------------------------
// IR types — what the code generator would receive
// ------------------------------------------------------------------

interface Annotation {
  kind: "requires" | "ensures" | "invariant" | "decreases" | "assert" | "import";
  expr: string;
  line: number;
}

interface ParamSpec {
  name: string;
  type: string;
}

interface WhileSpec {
  kind: "while";
  condition: string;
  invariants: string[];
  decreases: string | null;
  body: StatementSpec[];
  line: number;
}

interface IfSpec {
  kind: "if";
  condition: string;
  then: StatementSpec[];
  else: StatementSpec[];
  line: number;
}

interface LetSpec {
  kind: "let";
  name: string;
  mutable: boolean;
  type: string | null;
  init: string;
  line: number;
}

interface ReturnSpec {
  kind: "return";
  value: string;
  line: number;
}

interface AssignSpec {
  kind: "assign";
  target: string;
  value: string;
  line: number;
}

interface ExprStmtSpec {
  kind: "expr";
  text: string;
  line: number;
}

type StatementSpec = WhileSpec | IfSpec | LetSpec | ReturnSpec | AssignSpec | ExprStmtSpec;

interface FunctionSpec {
  name: string;
  params: ParamSpec[];
  returnType: string;
  requires: string[];
  ensures: string[];
  body: StatementSpec[];
  line: number;
}

interface ModuleSpec {
  file: string;
  imports: string[];
  functions: FunctionSpec[];
}

// ------------------------------------------------------------------
// Annotation parsing
// ------------------------------------------------------------------

const ANNOTATION_PREFIX = "//@ ";

function parseAnnotations(node: Node): Annotation[] {
  const annotations: Annotation[] = [];
  const ranges = node.getLeadingCommentRanges();

  for (const range of ranges) {
    const text = range.getText().trim();
    if (!text.startsWith(ANNOTATION_PREFIX)) continue;

    const content = text.slice(ANNOTATION_PREFIX.length);
    const spaceIdx = content.indexOf(" ");
    if (spaceIdx === -1) continue;

    const keyword = content.slice(0, spaceIdx);
    const expr = content.slice(spaceIdx + 1).trim();
    const line = range.getPos();

    const validKinds = ["requires", "ensures", "invariant", "decreases", "assert", "import"];
    if (validKinds.includes(keyword)) {
      annotations.push({ kind: keyword as Annotation["kind"], expr, line });
    }
  }

  return annotations;
}

// ------------------------------------------------------------------
// Statement extraction
// ------------------------------------------------------------------

function extractStatements(stmts: Node[]): StatementSpec[] {
  const result: StatementSpec[] = [];

  for (const stmt of stmts) {
    const line = stmt.getStartLineNumber();

    // Variable declaration
    if (Node.isVariableStatement(stmt)) {
      for (const decl of stmt.getDeclarations()) {
        const mutable = stmt.getDeclarationKind() === "let";
        result.push({
          kind: "let",
          name: decl.getName(),
          mutable,
          type: decl.getTypeNode()?.getText() ?? null,
          init: decl.getInitializer()?.getText() ?? "",
          line,
        });
      }
      continue;
    }

    // While loop
    if (Node.isWhileStatement(stmt)) {
      const whileStmt = stmt as WhileStatement;
      const annotations = parseAnnotations(stmt);
      // Also check for annotations on the first statement inside the loop body
      const bodyStmts = whileStmt.getStatement();
      let bodyAnnotations: Annotation[] = [];
      if (Node.isBlock(bodyStmts)) {
        const firstChild = bodyStmts.getStatements()[0];
        if (firstChild) {
          bodyAnnotations = parseAnnotations(firstChild);
        }
      }
      const allAnnotations = [...annotations, ...bodyAnnotations];

      const invariants = allAnnotations
        .filter((a) => a.kind === "invariant")
        .map((a) => a.expr);
      const decreases = allAnnotations.find((a) => a.kind === "decreases")?.expr ?? null;

      const body = Node.isBlock(bodyStmts)
        ? extractStatements(bodyStmts.getStatements())
        : [];

      result.push({
        kind: "while",
        condition: whileStmt.getExpression().getText(),
        invariants,
        decreases,
        body,
        line,
      });
      continue;
    }

    // If statement
    if (Node.isIfStatement(stmt)) {
      const thenStmt = stmt.getThenStatement();
      const elseStmt = stmt.getElseStatement();
      result.push({
        kind: "if",
        condition: stmt.getExpression().getText(),
        then: Node.isBlock(thenStmt)
          ? extractStatements(thenStmt.getStatements())
          : extractStatements([thenStmt]),
        else: elseStmt
          ? Node.isBlock(elseStmt)
            ? extractStatements(elseStmt.getStatements())
            : extractStatements([elseStmt])
          : [],
        line,
      });
      continue;
    }

    // Return
    if (Node.isReturnStatement(stmt)) {
      result.push({
        kind: "return",
        value: stmt.getExpression()?.getText() ?? "",
        line,
      });
      continue;
    }

    // Expression statement (assignments, function calls)
    if (Node.isExpressionStatement(stmt)) {
      const expr = stmt.getExpression();
      if (Node.isBinaryExpression(expr) && expr.getOperatorToken().getText() === "=") {
        result.push({
          kind: "assign",
          target: expr.getLeft().getText(),
          value: expr.getRight().getText(),
          line,
        });
      } else {
        result.push({
          kind: "expr",
          text: expr.getText(),
          line,
        });
      }
      continue;
    }

    // Fallback
    result.push({
      kind: "expr",
      text: stmt.getText(),
      line,
    });
  }

  return result;
}

// ------------------------------------------------------------------
// Function extraction
// ------------------------------------------------------------------

function extractFunction(fn: FunctionDeclaration): FunctionSpec {
  const annotations = parseAnnotations(fn);
  // Also check annotations on the first statement of the body
  const bodyStmts = fn.getBody()?.getStatements() ?? [];
  const firstStmtAnnotations = bodyStmts.length > 0 ? parseAnnotations(bodyStmts[0]) : [];
  const allAnnotations = [...annotations, ...firstStmtAnnotations];

  const requires = allAnnotations.filter((a) => a.kind === "requires").map((a) => a.expr);
  const ensures = allAnnotations.filter((a) => a.kind === "ensures").map((a) => a.expr);

  const params = fn.getParameters().map((p) => ({
    name: p.getName(),
    type: p.getTypeNode()?.getText() ?? "unknown",
  }));

  return {
    name: fn.getName() ?? "<anonymous>",
    params,
    returnType: fn.getReturnTypeNode()?.getText() ?? "unknown",
    requires,
    ensures,
    body: extractStatements(bodyStmts),
    line: fn.getStartLineNumber(),
  };
}

// ------------------------------------------------------------------
// Module extraction
// ------------------------------------------------------------------

function extractModule(sourceFile: SourceFile): ModuleSpec {
  // Collect top-level //@ import annotations
  const imports: string[] = [];
  const firstStmt = sourceFile.getStatements()[0];
  if (firstStmt) {
    const annotations = parseAnnotations(firstStmt);
    for (const a of annotations) {
      if (a.kind === "import") imports.push(a.expr);
    }
  }

  const functions = sourceFile
    .getFunctions()
    .map(extractFunction);

  return {
    file: sourceFile.getFilePath(),
    imports,
    functions,
  };
}

// ------------------------------------------------------------------
// Main
// ------------------------------------------------------------------

const filePath = process.argv[2];
if (!filePath) {
  console.error("Usage: npx tsx src/extract.ts <file.ts>");
  process.exit(1);
}

const project = new Project({
  compilerOptions: { strict: true },
});

const sourceFile = project.addSourceFileAtPath(filePath);
const spec = extractModule(sourceFile);

console.log(JSON.stringify(spec, null, 2));
