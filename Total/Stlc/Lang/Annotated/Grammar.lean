import Total.Core

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  inductive Ty: Type where
    | bool: Ty
    | nat: Ty
    | fn {α: Nat} (dom: Domain Ty α) (rng: Ty): Ty

  abbrev Domain (α: Nat) := _root_.Domain Ty α

  inductive PrimOp: {α: Nat} → Domain α → Ty → Type where
    | and: PrimOp (.cons .bool (.nil .bool)) .bool
    | or:  PrimOp (.cons .bool (.nil .bool)) .bool
    | not: PrimOp (.nil .bool) .bool

    | add: PrimOp (.cons .nat (.nil .nat)) .nat
    | sub: PrimOp (.cons .nat (.nil .nat)) .nat
    | mul: PrimOp (.cons .nat (.nil .nat)) .nat

    | eq  {τ: Ty}: PrimOp (.cons τ (.nil τ)) .bool
    | neq {τ: Ty}: PrimOp (.cons τ (.nil τ)) .bool

    | lt:  PrimOp (.cons .nat (.nil .nat)) .bool
    | lte: PrimOp (.cons .nat (.nil .nat)) .bool
    | gt:  PrimOp (.cons .nat (.nil .nat)) .bool
    | gte: PrimOp (.cons .nat (.nil .nat)) .bool

  inductive Term: Ty → Type where
    | bool (b: Bool): Term .bool
    | nat (n: Nat): Term .nat
    | primOp {α: Nat} {δ: Domain α} {τ: Ty} (op: PrimOp δ τ) (operands: Args Term δ): Term (.fn δ τ)
    | cond {τ: Ty} (c: Term .bool) (t f: Term τ): Term τ

  abbrev Args {α: Nat} (δ: Domain α) := _root_.Args Term δ

  inductive Top: Ty → Type where
end Total.Stlc.Lang.Annotated
