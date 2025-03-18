import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  namespace PrimOp
    inductive Eval₁: (α: Nat) → (π: Domain Ty α) → (τ: Ty) → PrimOp α π τ → Term τ → Prop where
  end PrimOp

  namespace Term
    inductive IsValue: (τ: Ty) → Term τ → Prop where
      | bool (b: Bool): IsValue .bool (.bool b)
      | nat  (n: Nat):  IsValue .nat (.nat n)
      -- | var (id: Ident): IsValue τ (.var id)
      -- | abs {α: Nat} {π: Params Ty α} {τ: Ty} (formals: Params Ident Ty α π) (body: Term τ): IsValue (.fn π τ) (.abs formals body)

    inductive Eval₁ (τ: Ty): Term τ → Term τ → Prop where

    def Eval (τ: Ty) := RTC (Eval₁ τ)
  end Term

  namespace Top
    inductive IsValue (τ: Ty): Top τ → Prop where
    inductive Eval₁ (τ: Ty): Top τ → Top τ → Prop where
    def Eval (τ: Ty) := RTC (Eval₁ τ)
  end Top
end Total.Stlc.Lang.Annotated
