import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  namespace PrimOp
    inductive Eval₁: {α: Nat} → {δ: Domain α} → {τ: Ty} → PrimOp δ τ → Args δ → Term τ → Prop where
  end PrimOp

  namespace Value
    inductive IsValue: {τ: Ty} → Value τ → Prop where
      | bool (b: Bool): IsValue (.bool b)
      | nat  (n: Nat):  IsValue (.nat n)
  end Value

  namespace Term
    inductive IsValue: {τ: Ty} → Term τ → Prop where
      | value {τ: Ty} (v: Value τ): IsValue (.value v)

    inductive Eval₁: {τ: Ty} → Term τ → Term τ → Prop where

    abbrev Eval {τ: Ty}: Term τ → Term τ → Prop := RTC Eval₁
  end Term

  namespace Top
    inductive IsValue: {τ: Ty} → Top τ → Prop where
    inductive Eval₁: {τ: Ty} → Top τ → Top τ → Prop where
    abbrev Eval {τ: Ty}: Top τ → Top τ → Prop := RTC Eval₁
  end Top
end Total.Stlc.Lang.Annotated
