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

  namespace PrimOp
    @[reducible]
    def Halts {ρ: Ty → Type} (τ: Ty) (p: PrimOp) (t₁: Term ρ τ): Prop := ∃ t₂: Term ρ τ, Eval₁ p t₁ t₂ ∧ Term.IsValue t₂

    @[reducible]
    def Total {ρ: Ty → Type} (τ₁ τ₂: Ty) (op: UnOp) (t: Term ρ): Prop :=
      (HasType op τ₁ τ₂) ∧ (Halts op t) ∧ True

    namespace Total
      theorem halts {τ₁ τ₂: Ty} {op: UnOp} {t: Term}: Total τ₁ τ₂ op t → Halts op t
        | ⟨_, hh, _⟩ => hh
    end Total
  end PrimOp

  namespace Term
    @[reducible]
    def Halts {ρ: Ty → Type} {τ: Ty} (t₁: Term ρ τ): Prop := ∃ t₂: Term ρ τ, Eval ρ τ t₁ t₂ ∧ IsValue ρ τ t₂

    @[reducible]
    def Total {ρ: Ty → Type} (τ: Ty) (t: Term ρ τ): Prop :=
      (Halts t) ∧ (
        match τ with
          | .bool => True
          | .nat  => True
          | .fn _ _ => sorry
      )

    namespace IsValue
      theorem halts {ρ: Ty → Type} {τ: Ty} {t: Term ρ τ}: IsValue ρ τ t → Halts t
        | .bool _ => ⟨_, .refl, .bool _⟩
        | .nat  _ => ⟨_, .refl, .nat  _⟩
    end IsValue

    namespace Total
      theorem halts {ρ: Ty → Type} {τ: Ty}: {t: Term ρ τ} → Total τ t → Halts t
        | .bool _, _ => IsValue.halts (.bool _)
        | .nat _,  _ => IsValue.halts (.nat  _)

        | .primOp _, _ => sorry

        | .cond _ _ _,  ⟨_, ⟨_, he, hv⟩, _⟩ => ⟨_, he, hv⟩
    end Total
  end Term

  namespace Top
    @[reducible]
    def Halts {ρ: Ty → Type} {τ: Ty} (t₁: Top ρ τ): Prop := ∃ t₂: Top ρ τ, Eval ρ τ t₁ t₂ ∧ IsValue ρ τ t₂

    @[reducible]
    def Total {ρ: Ty → Type} {τ: Ty}: Ty → Top ρ τ → Prop
      | .bool, t => nomatch t

    namespace IsValue
      theorem halts {ρ: Ty → Type} {τ: Ty} {t: Top ρ τ}: IsValue ρ τ t → Halts t := nomatch t
    end IsValue

    namespace Total
      theorem halts {ρ: Ty → Type} {τ: Ty} {t: Top ρ τ}: Top ρ τ → Halts t
        | t => nomatch t
    end Total
  end Top
end Total.Stlc.Lang.Annotated
