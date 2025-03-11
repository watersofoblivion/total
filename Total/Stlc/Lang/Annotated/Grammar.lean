import Total.Core

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

  inductive Term (ρ: Ty → Type): Ty → Type where
    | bool (b: Bool): Term ρ .bool
    | nat (n: Nat): Term ρ .nat
    | primOp {α: Nat} {δ: Domain Ty α} {τ: Ty} (op: PrimOp α δ τ): Term ρ (.fn δ τ)
    | cond {τ: Ty} (c: Term ρ .bool) (t f: Term ρ τ): Term ρ τ
    -- | var {τ: Ty} (id: Ident): Term ρ τ
    -- | bind {τ σ: Ty} (id: Ident) (expr: Term ρ τ) (scope: Term ρ σ): Term ρ σ
    -- | abs {α: Nat} {δ: Domain Ty α} {τ: Ty} (formals: Formals Ident Ty α δ) (body: Term ρ τ): Term ρ (.fn δ τ)
    -- | app {α: Nat} {δ: Domain Ty α} {τ: Ty} (fn: Term ρ (.fn δ τ)) (args: Args Ty (Term ρ) α δ): Term ρ τ

  inductive Top (ρ: Ty → Type): Ty → Type where
    -- | val (ι: Ident) (τ: Ty) (ε: Term ρ τ): Top ρ τ
    -- | defn {α: Nat} {π: Params Ty α} {τ: Ty} (ι: Ident) (params: Formals Ident Ty α π) (body: Term ρ τ): Top ρ τ
end Total.Stlc.Lang.Annotated
