import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax
import Total.Stlc.Lang.Surface.Semantics

set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  namespace UnOp
    @[reducible]
    def Halts (op: UnOp) (t₁: Term): Prop := ∃ t₂: Term, Eval₁ op t₁ t₂ ∧ Term.IsValue t₂

    @[reducible]
    def Total (τ₁ τ₂: Ty) (op: UnOp) (t: Term): Prop :=
      (HasType op τ₁ τ₂) ∧ (Halts op t) ∧ True

    namespace Total
      theorem halts {τ₁ τ₂: Ty} {op: UnOp} {t: Term}: Total τ₁ τ₂ op t → Halts op t
        | ⟨_, hh, _⟩ => hh
    end Total
  end UnOp

  namespace BinOp
    @[reducible]
    def Halts (op: BinOp) (t₁ t₂: Term): Prop := ∃ t₃: Term, Eval₁ op t₁ t₂ t₃ ∧ Term.IsValue t₃

    @[reducible]
    def Total (τ₁ τ₂ τ₃: Ty) (op: BinOp) (t₁ t₂: Term): Prop :=
      (HasType op τ₁ τ₂ τ₃) ∧ (Halts op t₁ t₂) ∧ True

    namespace Total
      theorem halts {τ₁ τ₂ τ₃: Ty} {op: BinOp} {t₁ t₂: Term}: Total τ₁ τ₂ τ₃ op t₁ t₂ → Halts op t₁ t₂
        | ⟨_, hh, _⟩ => hh
    end Total
  end BinOp

  namespace Term
    @[reducible]
    def Halts (t₁: Term): Prop := ∃ t₂: Term, Eval t₁ t₂ ∧ IsValue t₂

    @[reducible]
    def Total (τ: Ty) (t: Term): Prop :=
      (HasType t τ) ∧ (Halts t) ∧ (
        match τ with
          | .bool => True
          | .nat  => True
      )

    namespace IsValue
      theorem halts {t: Term}: IsValue t → Halts t
        | .bool _ => ⟨_, .refl, .bool _⟩
        | .nat  _ => ⟨_, .refl, .nat  _⟩
    end IsValue

    namespace Total
      theorem halts {τ: Ty}: {t: Term} → Total τ t → Halts t
        | .bool _, _ => IsValue.halts (.bool _)
        | .nat _,  _ => IsValue.halts (.nat  _)

        | .unOp _ _,    ⟨_, ⟨_, he, hv⟩, _⟩
        | .binOp _ _ _, ⟨_, ⟨_, he, hv⟩, _⟩

        | .cond _ _ _,  ⟨_, ⟨_, he, hv⟩, _⟩ => ⟨_, he, hv⟩
    end Total
  end Term

  namespace Top
    @[reducible]
    def Halts (t₁: Top): Prop := ∃ t₂: Top, Eval t₁ t₂ ∧ IsValue t₂

    @[reducible]
    def Total: Ty → Top → Prop
      | .bool, t => nomatch t

    namespace IsValue
      theorem halts {t: Top}: IsValue t → Halts t := nomatch t
    end IsValue

    namespace Total
      theorem halts {τ: Ty} {t: Top}: Top → Halts t
        | t => nomatch t
    end Total
  end Top
end Total.Stlc.Lang.Surface
