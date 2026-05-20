//@ backend dafny

/**
 * Preorder tree traversal — iterative stack-based implementation
 * verified against the pure recursive specification.
 *
 * Adapted from https://github.com/hath995/dafny-aoc-2025/preorder.dfy.
 *
 * - `Tree` is a recursive discriminated union (Node | Nil).
 * - `preorderTraversal(root)` is the pure functional specification.
 * - `childStack(node)` pushes right before left, so left pops first.
 * - `traverseBasic(root)` is the imperative version that returns the
 *   same sequence as `preorderTraversal(root)`.
 *
 * The supporting proof scaffolding — `nodeSet`, `validNode`,
 * `UnionNodes`, `StackToPreorder`, `AllDisjoint` and the associated
 * lemmas — lives in preorder.dfy above the generated method.
 * The TS-side `requires` is just the kind check; the validity
 * precondition is added in the hand-written .dfy.
 */

type Tree =
  | { kind: "Nil" }
  | { kind: "Node"; val: number; left: Tree; right: Tree }

//@ pure
export function preorderTraversal(root: Tree): Tree[] {
  if (root.kind === "Nil") return [];
  if (root.left.kind !== "Nil" && root.right.kind !== "Nil") {
    return [root, ...preorderTraversal(root.left), ...preorderTraversal(root.right)];
  }
  if (root.left.kind !== "Nil") {
    return [root, ...preorderTraversal(root.left)];
  }
  if (root.right.kind !== "Nil") {
    return [root, ...preorderTraversal(root.right)];
  }
  return [root];
}

//@ pure
export function childStack(node: Tree): Tree[] {
  if (node.kind === "Nil") return [];
  if (node.right.kind === "Node" && node.left.kind === "Node") {
    return [node.right, node.left];
  }
  if (node.right.kind === "Node") {
    return [node.right];
  }
  if (node.left.kind === "Node") {
    return [node.left];
  }
  return [];
}

export function traverseBasic(root: Tree): Tree[] {
  //@ requires root.kind === "Node"
  //@ ensures \result === preorderTraversal(root)
  let result: Tree[] = [];
  let stack: Tree[] = [root];
  while (stack.length > 0) {
    //@ invariant forall(s: Tree, s in stack ==> s.kind === "Node")
    const current = stack[stack.length - 1];
    stack = [...stack.slice(0, stack.length - 1), ...childStack(current)];
    result = [...result, current];
  }
  return result;
}
