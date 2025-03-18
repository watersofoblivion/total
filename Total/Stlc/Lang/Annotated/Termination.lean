import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax
import Total.Stlc.Lang.Annotated.Semantics

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  namespace PrimOp
    @[reducible]
    def Halts (τ: Ty) (p: PrimOp) (t₁: Term τ): Prop := ∃ t₂: Term τ, Eval₁ t₁ t₂ ∧ Term.IsValue t₂

    @[reducible]
    def Total (τ₁ τ₂: Ty) (op: UnOp) (t: Term): Prop :=
      (HasType op τ₁ τ₂) ∧ (Halts op t) ∧ True

    namespace Total
      theorem halts {τ₁ τ₂: Ty} {op: UnOp} {t: Term}: Total τ₁ τ₂ op t → Halts op t
        | ⟨_, hh, _⟩ => hh
    end Total
  end PrimOp

  namespace Term
    @[reducible]
    def Halts {τ: Ty} (t₁: Term τ): Prop := ∃ t₂: Term τ, Eval τ t₁ t₂ ∧ IsValue τ t₂

    @[reducible]
    def Total (τ: Ty) (t: Term τ): Prop :=
      (Halts t) ∧ (
        match τ with
          | .bool => True
          | .nat  => True
          | .fn _ _ => sorry
      )

    namespace IsValue
      theorem halts {τ: Ty} {t: Term τ}: IsValue τ t → Halts t
        | .bool _ => ⟨_, .refl, .bool _⟩
        | .nat  _ => ⟨_, .refl, .nat  _⟩
    end IsValue

    namespace Total
      theorem halts {τ: Ty}: {t: Term τ} → Total τ t → Halts t
        | .bool _, _ => IsValue.halts (.bool _)
        | .nat _,  _ => IsValue.halts (.nat  _)

        | .primOp _, _ => sorry

        | .cond _ _ _,  ⟨_, ⟨_, he, hv⟩, _⟩ => ⟨_, he, hv⟩
    end Total
  end Term

  namespace Top
    @[reducible]
    def Halts {τ: Ty} (t₁: Top τ): Prop := ∃ t₂: Top τ, Eval τ t₁ t₂ ∧ IsValue τ t₂

    @[reducible]
    def Total {τ: Ty}: Ty → Top τ → Prop
      | .bool, t => nomatch t

    namespace IsValue
      theorem halts {τ: Ty} {t: Top τ}: IsValue τ t → Halts t := nomatch t
    end IsValue

    namespace Total
      theorem halts {τ: Ty} {t: Top τ}: Top τ → Halts t
        | t => nomatch t
    end Total
  end Top
end Total.Stlc.Lang.Annotated
