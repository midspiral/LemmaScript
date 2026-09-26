//@ backend fstar

/**
 * A verified compiler from expression trees to continuation-passing closures.
 *
 * compile(expression)(environment, continuation) agrees with interpreting the
 * expression and handing its value to the continuation, for every environment
 * and every pure continuation. Compilation folds constants and removes x * 0.
 * The generated closures contain no calls to the interpreter.
 *
 * Variable names are numbers. A let binding shadows that name only in its body;
 * its right-hand side still sees the outer environment. Values use bigint for
 * exact arithmetic; environments and continuations must be pure and terminating.
 */

export type Expression =
  | { kind: "literal"; value: bigint }
  | { kind: "variable"; name: number }
  | { kind: "add"; left: Expression; right: Expression }
  | { kind: "multiply"; left: Expression; right: Expression }
  | { kind: "let"; name: number; value: Expression; body: Expression };

export type Environment = (name: number) => bigint;
export type Continuation = (value: bigint) => bigint;
export type Code = (environment: Environment, continuation: Continuation) => bigint;

export function bind(environment: Environment, name: number, value: bigint): Environment {
  //@ ensures forall(query: int, \result(query) === (query === name ? value : environment(query)))
  return (query: number): bigint => query === name ? value : environment(query);
}

export function evaluate(expression: Expression, environment: Environment): bigint {
  switch (expression.kind) {
    case "literal":
      return expression.value;
    case "variable":
      return environment(expression.name);
    case "add":
      return evaluate(expression.left, environment) + evaluate(expression.right, environment);
    case "multiply":
      return evaluate(expression.left, environment) * evaluate(expression.right, environment);
    case "let":
      return evaluate(expression.body, bind(environment, expression.name, evaluate(expression.value, environment)));
  }
}

export function compile(expression: Expression): Code {
  //@ ensures forall(environment: Environment, forall(continuation: Continuation, \result(environment, continuation) === continuation(evaluate(expression, environment))))
  switch (expression.kind) {
    case "literal":
      return (environment: Environment, continuation: Continuation): bigint => continuation(expression.value);
    case "variable":
      return (environment: Environment, continuation: Continuation): bigint => continuation(environment(expression.name));
    case "add": {
      if (expression.left.kind === "literal" && expression.right.kind === "literal") {
        const folded = expression.left.value + expression.right.value;
        return (environment: Environment, continuation: Continuation): bigint => continuation(folded);
      }
      const left = compile(expression.left);
      const right = compile(expression.right);
      return (environment: Environment, continuation: Continuation): bigint =>
        left(environment, (x: bigint): bigint => right(environment, (y: bigint): bigint => continuation(x + y)));
    }
    case "multiply": {
      if (expression.right.kind === "literal" && expression.right.value === 0n) {
        return (environment: Environment, continuation: Continuation): bigint => continuation(0n);
      }
      if (expression.left.kind === "literal" && expression.right.kind === "literal") {
        const folded = expression.left.value * expression.right.value;
        return (environment: Environment, continuation: Continuation): bigint => continuation(folded);
      }
      const left = compile(expression.left);
      const right = compile(expression.right);
      return (environment: Environment, continuation: Continuation): bigint =>
        left(environment, (x: bigint): bigint => right(environment, (y: bigint): bigint => continuation(x * y)));
    }
    case "let": {
      const value = compile(expression.value);
      const body = compile(expression.body);
      return (environment: Environment, continuation: Continuation): bigint =>
        value(environment, (x: bigint): bigint => body(bind(environment, expression.name, x), continuation));
    }
  }
}

export function run(expression: Expression, environment: Environment): bigint {
  //@ ensures \result === evaluate(expression, environment)
  return compile(expression)(environment, (value: bigint): bigint => value);
}

// Compile "let x = x + 1 in (let x = x * 2 in x) + x" once, then reuse it.
// The inner x does not escape: the expression is 3 * (outer x + 1).
export function shadowingDemo(x: bigint): bigint {
  //@ ensures \result === 30n * (x + 1n) + 1n
  const program: Expression = {
    kind: "let", name: 0,
    value: { kind: "add", left: { kind: "variable", name: 0 }, right: { kind: "literal", value: 1n } },
    body: {
      kind: "add",
      left: {
        kind: "let", name: 0,
        value: { kind: "multiply", left: { kind: "variable", name: 0 }, right: { kind: "literal", value: 2n } },
        body: { kind: "variable", name: 0 },
      },
      right: { kind: "variable", name: 0 },
    },
  };
  const code = compile(program);
  const environment = (name: number): bigint => name === 0 ? x : 0n;
  const answer = code(environment, (value: bigint): bigint => value);
  const transformed = code(environment, (value: bigint): bigint => 10n * value + 1n);
  //@ assert transformed === 10n * answer + 1n
  return transformed;
}
