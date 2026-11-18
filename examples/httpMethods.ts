export const methods = ["get", "post"];

const firstMethods = ["get"];
export const extraMethods = [...firstMethods, "post", "delete"] as const;
export const emptyMethods: readonly string[] = [];

export function isBaseMethod(method: string): boolean {
  //@ verify
  //@ ensures \result <==> (method === "get" || method === "post")
  return methods.includes(method);
}
