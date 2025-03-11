import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax

namespace Total.Stlc.Lang.Annotated
  namespace PrimOp
    inductive Eval₁ (ρ: Ty → Type): (α: Nat) → (π: Domain Ty α) → (τ: Ty) → PrimOp α π τ → Term ρ τ → Prop where
  end PrimOp

  namespace Term
    inductive IsValue (ρ: Ty → Type): (τ: Ty) → Term ρ τ → Prop where
      | bool (b: Bool): IsValue ρ .bool (.bool b)
      | nat (n: Nat): IsValue ρ .nat (.nat n)
      -- | var (id: Ident): IsValue ρ τ (.var id)
      -- | abs {α: Nat} {π: Params Ty α} {τ: Ty} (formals: Formals Ident Ty α π) (body: Term ρ τ): IsValue ρ (.fn π τ) (.abs formals body)

    inductive Eval₁ (ρ: Ty → Type) (τ: Ty): Term ρ τ → Term ρ τ → Prop where
    def Eval (ρ: Ty → Type) (τ: Ty) := RTC (Eval₁ ρ τ)
  end Term

  namespace Top
    inductive IsValue (ρ: Ty → Type) (τ: Ty): Top ρ τ → Prop where
    inductive Eval₁ (ρ: Ty → Type) (τ: Ty): Top ρ τ → Top ρ τ → Prop where
    def Eval (ρ: Ty → Type) (τ: Ty) := RTC (Eval₁ ρ τ)
  end Top
end Total.Stlc.Lang.Annotated
