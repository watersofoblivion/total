import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax
import Total.Stlc.Lang.Annotated.Semantics

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  namespace PrimOp
    @[reducible]
    def Halts {α: Nat} {δ: Domain α} {τ: Ty} (op: PrimOp δ τ) (args: Values δ): Prop := ∃ t₂: Term τ, Eval₁ op args t₂ ∧ Term.IsValue t₂

    @[reducible]
    def Total {α: Nat} {δ: Domain α} {τ: Ty} (op: PrimOp δ τ) (args: Values δ): Prop :=
      (Halts op args) ∧ True

    namespace Total
      theorem halts {α: Nat} {δ: Domain α} {τ: Ty} {op: PrimOp δ τ} {args: Values δ}: Total op args → Halts op args
        | ⟨hh, _⟩ => hh
    end Total
  end PrimOp

  namespace Term
    @[reducible]
    def Halts {τ: Ty} (t₁: Term τ): Prop := ∃ t₂: Term τ, Eval t₁ t₂ ∧ IsValue t₂

    @[reducible]
    def Total {τ: Ty} (t: Term τ): Prop :=
      (Halts t) ∧ (
        match τ with
          | .bool => True
          | .nat  => True
          | .fn _ _ => sorry
      )

    namespace IsValue
      theorem halts {τ: Ty} {t: Term τ}: IsValue t → Halts t := sorry
        -- | .bool _ => ⟨_, .refl, .bool _⟩
        -- | .nat  _ => ⟨_, .refl, .nat  _⟩
    end IsValue

    namespace Total
      theorem halts {τ: Ty}: {t: Term τ} → Total t → Halts t := sorry
        -- | .bool _, _ => IsValue.halts (.bool _)
        -- | .nat _,  _ => IsValue.halts (.nat  _)

        -- | .primOp _ _, _ => sorry

        -- | .cond _ _ _,  _ => sorry
    end Total
  end Term

  namespace Args
    @[reducible]
    def Halts {α: Nat} {δ: Domain α} (a₁: Args δ): Prop := ∃ a₂: Args δ, Eval a₁ a₂ ∧ IsValue a₂

    @[reducible]
    def Total {α: Nat} {δ: Domain α} (t: Args δ): Prop :=
      (Halts t) ∧ (
        match δ with
          | _ => True
      )

    namespace IsValue
      theorem halts {α: Nat} {δ: Domain α} {t: Args δ}: IsValue t → Halts t := sorry
    end IsValue

    namespace Total
      theorem halts {α: Nat} {δ: Domain α}: {t: Args δ} → Total t → Halts t := sorry
    end Total
  end Args

  namespace Top
    @[reducible]
    def Halts {τ: Ty} (t₁: Top τ): Prop := ∃ t₂: Top τ, Eval t₁ t₂ ∧ IsValue t₂

    @[reducible]
    def Total {τ: Ty}: Ty → Top τ → Prop
      | _, t => nomatch t

    namespace IsValue
      theorem halts {τ: Ty} {t: Top τ}: IsValue t → Halts t := nomatch t
    end IsValue

    namespace Total
      theorem halts {τ: Ty} {t: Top τ}: Top τ → Halts t
        | t => nomatch t
    end Total
  end Top
end Total.Stlc.Lang.Annotated
