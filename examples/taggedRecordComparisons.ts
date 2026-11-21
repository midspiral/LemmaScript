//@ backend dafny

// Inline tagged defaults retain their union, enum, and nested record types.
// Compare primitive fields: whole-object === uses reference identity in JS.

export type Channel = "email" | "sms";
export type Recipient = { address: string };
export type Delivery =
  | { tag: "queued"; channel: Channel; recipient: Recipient }
  | { tag: "sent"; channel: Channel; recipient: Recipient };

// An asserted tagged literal on the right, with an enum-valued field.
export function usesEmailChannel(delivery: Delivery): boolean {
  //@ ensures \result === (delivery.channel === "email")
  return delivery.channel ===
    ({ tag: "queued", channel: "email", recipient: { address: "" } } as Delivery).channel;
}

// An asserted tagged literal on the left, with a nested record payload.
export function hasDifferentRecipient(delivery: Delivery, recipient: Recipient): boolean {
  //@ ensures \result === (recipient.address !== delivery.recipient.address)
  return ({ tag: "queued", channel: "email", recipient } as Delivery).recipient.address !==
    delivery.recipient.address;
}

// Send exactly the queued email deliveries that have a nonempty address.
export function shouldSendEmail(delivery: Delivery): boolean {
  //@ ensures \result === (delivery.tag === "queued" && delivery.channel === "email" && delivery.recipient.address !== "")
  if (delivery.tag === "sent") return false;
  return usesEmailChannel(delivery) && hasDifferentRecipient(delivery, { address: "" });
}
