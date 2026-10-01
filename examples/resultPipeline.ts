//@ backend dafny,fstar

// A validation pipeline built from pure, total callbacks and tagged results.
export type Result<A, E> =
  | { _tag: "Success"; success: A }
  | { _tag: "Failure"; failure: E };

export function succeed<A, E>(success: A): Result<A, E> {
  return { _tag: "Success", success };
}

export function fail<A, E>(failure: E): Result<A, E> {
  return { _tag: "Failure", failure };
}

export function map<A, B, E>(self: Result<A, E>, f: (value: A) => B): Result<B, E> {
  //@ ensures self._tag === "Failure" ==> (\result._tag === "Failure" && \result.failure === self.failure)
  //@ ensures self._tag === "Success" ==> (\result._tag === "Success" && \result.success === f(self.success))
  if (self._tag === "Failure") return fail<B, E>(self.failure);
  return succeed<B, E>(f(self.success));
}

export function flatMap<A, B, E>(self: Result<A, E>, f: (value: A) => Result<B, E>): Result<B, E> {
  //@ ensures self._tag === "Failure" ==> (\result._tag === "Failure" && \result.failure === self.failure)
  //@ ensures self._tag === "Success" ==> \result === f(self.success)
  if (self._tag === "Failure") return fail<B, E>(self.failure);
  return f(self.success);
}

export interface Order {
  quantity: number;
  unitPrice: number;
}

export function checkQuantity(order: Order): Result<Order, string> {
  //@ ensures order.quantity <= 0 ==> (\result._tag === "Failure" && \result.failure === "invalid quantity")
  //@ ensures order.quantity > 0 ==> (\result._tag === "Success" && \result.success === order)
  if (order.quantity <= 0) return fail<Order, string>("invalid quantity");
  return succeed<Order, string>(order);
}

export function checkPrice(order: Order): Result<Order, string> {
  //@ ensures order.unitPrice < 0 ==> (\result._tag === "Failure" && \result.failure === "invalid price")
  //@ ensures order.unitPrice >= 0 ==> (\result._tag === "Success" && \result.success === order)
  if (order.unitPrice < 0) return fail<Order, string>("invalid price");
  return succeed<Order, string>(order);
}

export function priceOrder(order: Order): Result<number, string> {
  //@ ensures order.quantity <= 0 ==> (\result._tag === "Failure" && \result.failure === "invalid quantity")
  //@ ensures order.quantity > 0 && order.unitPrice < 0 ==> (\result._tag === "Failure" && \result.failure === "invalid price")
  //@ ensures (\result._tag === "Success") <==> (order.quantity > 0 && order.unitPrice >= 0)
  //@ ensures \result._tag === "Success" ==> \result.success === order.quantity * order.unitPrice
  const checked = flatMap(checkQuantity(order), checkPrice);
  return map(checked, (valid: Order): number => valid.quantity * valid.unitPrice);
}
