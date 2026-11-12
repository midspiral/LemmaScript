/** Parameter scope exists before parameter initialization. Keep binding identity,
 * initialization order, and closure dependencies separate until all three can
 * be represented by ordinary immutable backend lets. */
import type { TExpr, TStmt, Ty } from "./typedir.js";

export interface CallbackBinding {
  readonly name: string;
  ty: Ty;
  initialized: boolean;
  available: boolean;
  captured: boolean;
  assigned: boolean;
}

interface PendingClosure {
  binding: CallbackBinding;
  init: Extract<TExpr, { kind: "lambda" }>;
  captures: Set<CallbackBinding>;
}

export class CallbackBindings {
  readonly bindings: CallbackBinding[];
  readonly prefix: TStmt[] = [];
  private pending: PendingClosure[] = [];

  constructor(params: { name: string; ty: Ty }[]) {
    this.bindings = params.map(p => ({ ...p, initialized: false, available: false,
      captured: false, assigned: false }));
  }

  read(binding: CallbackBinding, captures?: Set<CallbackBinding>): void {
    if (captures) {
      captures.add(binding);
      binding.captured = true;
      return;
    }
    if (!binding.initialized) {
      throw new Error(`callback parameter '${binding.name}' is read before initialization`);
    }
    if (!binding.available) {
      throw new Error(`callback closure '${binding.name}' is used before its captured parameters are available`);
    }
  }

  write(binding: CallbackBinding, captures?: Set<CallbackBinding>): void {
    this.read(binding, captures);
    binding.assigned = true;
  }

  initialize(binding: CallbackBinding, init?: TExpr, captures?: Set<CallbackBinding>): void {
    binding.initialized = true;
    if (init?.kind === "lambda" && captures) {
      // Creating a lambda runs no source computation. Delay only that creation
      // until its immutable captures exist; never move a call or another default
      // expression. An earlier use of the closure fails read() above.
      this.pending.push({ binding, init, captures });
    } else {
      if (init) this.emit(binding, init);
      else binding.available = true;
    }
    this.flush();
  }

  private emit(binding: CallbackBinding, init: TExpr): void {
    this.prefix.push({ kind: "let", name: binding.name, ty: binding.ty, mutable: false, init });
    binding.available = true;
  }

  private flush(): void {
    // Repeatedly discharge dependencies: a newly available value can release
    // a closure which, in turn, releases another closure. Identities are object
    // references, so same-named bindings in nested callbacks cannot collide.
    let progress = true;
    while (progress) {
      progress = false;
      this.pending = this.pending.filter(p => {
        if (![...p.captures].every(b => b.available)) return true;
        this.emit(p.binding, p.init);
        progress = true;
        return false;
      });
    }
  }

  finishInitialization(): void {
    if (this.pending.length) {
      throw new Error(`callback default closure '${this.pending[0].binding.name}' needs a recursive closure environment`);
    }
  }

  checkCaptures(): void {
    for (const b of this.bindings) {
      if (b.captured && b.assigned) {
        throw new Error(`captured callback parameter '${b.name}' is assigned; a shared mutable closure environment is required`);
      }
    }
  }
}
