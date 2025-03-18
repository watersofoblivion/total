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
    | primOp {α: Nat} {δ: Domain Ty α} {τ: Ty} (op: PrimOp α δ τ) (operands: Args Ty (Term) α δ): Term (.fn δ τ)
    | cond {τ: Ty} (c: Term .bool) (t f: Term τ): Term τ
    -- | var {τ: Ty} (id: Ident): Term τ
    -- | bind {τ σ: Ty} (id: Ident) (expr: Term τ) (scope: Term σ): Term σ
    -- | abs {α: Nat} {δ: Domain Ty α} {τ: Ty} (formals: Params Ident Ty α δ) (body: Term τ): Term (.fn δ τ)
    -- | app {α: Nat} {δ: Domain Ty α} {τ: Ty} (fn: Term (.fn δ τ)) (args: Args Ty (Term) α δ): Term τ

  inductive Top: Ty → Type where
    -- | val (ι: Ident) (τ: Ty) (ε: Term τ): Top τ
    -- | defn {α: Nat} {π: Params Ty α} {τ: Ty} (ι: Ident) (params: Params Ident Ty α π) (body: Term τ): Top τ
end Total.Stlc.Lang.Annotated
