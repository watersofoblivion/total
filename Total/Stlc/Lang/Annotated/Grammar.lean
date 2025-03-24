import Total.Core

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  inductive Ty: Type where
    | bool: Ty
    | nat: Ty
    | fn {α: Nat} (dom: Domain Ty α) (rng: Ty): Ty

  inductive PrimOp: (α: Nat) → Domain Ty α → Ty → Type where
    | and: PrimOp 2 (.cons .bool (.nil .bool)) .bool
    | or:  PrimOp 2 (.cons .bool (.nil .bool)) .bool
    | not: PrimOp 1 (.nil .bool) .bool

    | add: PrimOp 2 (.cons .nat (.nil .nat)) .nat
    | sub: PrimOp 2 (.cons .nat (.nil .nat)) .nat
    | mul: PrimOp 2 (.cons .nat (.nil .nat)) .nat

    | eq  {τ: Ty}: PrimOp 2 (.cons τ (.nil τ)) .bool
    | neq {τ: Ty}: PrimOp 2 (.cons τ (.nil τ)) .bool

    | lt:  PrimOp 2 (.cons .nat (.nil .nat)) .bool
    | lte: PrimOp 2 (.cons .nat (.nil .nat)) .bool
    | gt:  PrimOp 2 (.cons .nat (.nil .nat)) .bool
    | gte: PrimOp 2 (.cons .nat (.nil .nat)) .bool

  inductive Term: Ty → Type where
    | bool (b: Bool): Term .bool
    | nat (n: Nat): Term .nat
    | primOp {α: Nat} {δ: Domain Ty α} {τ: Ty} (op: PrimOp α δ τ) (operands: Args Ty α δ): Term (.fn δ τ)
    | cond {τ: Ty} (c: Term .bool) (t f: Term τ): Term τ

  inductive Top: Ty → Type where
end Total.Stlc.Lang.Annotated
