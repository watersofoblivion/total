import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax
import Total.Stlc.Lang.Annotated.Semantics

namespace Total.Stlc.Lang.Annotated
  namespace Ty
  end Ty

  namespace Term
      namespace Eval₁
        theorem deterministic {ρ: Ty → Type} {τ: Ty} {t t₁ t₂: Term ρ τ}: Eval₁ ρ τ t t₁ → Eval₁ ρ τ t t₂ → t₁ = t₂ := sorry
        theorem progress {ρ: Ty → Type} {τ: Ty} {t₁: Term ρ τ}: IsValue ρ τ t₁ ∨ ∃ t₂: Term ρ τ, Eval₁ ρ τ t₁ t₂ := sorry

        -- TODO: Theorems for Strong Normalization
      end Eval₁
  end Term

  namespace Top
      namespace Eval₁
        theorem deterministic {ρ: Ty → Type} {τ: Ty} {t t₁ t₂: Top ρ τ}: Eval₁ ρ τ t t₁ → Eval₁ ρ τ t t₂ → t₁ = t₂ := sorry
        theorem progress {ρ: Ty → Type} {τ: Ty} {t₁: Top ρ τ}: IsValue ρ τ t₁ ∨ ∃ t₂: Top ρ τ, Eval₁ ρ τ t₁ t₂ := sorry
      end Eval₁
  end Top
end Total.Stlc.Lang.Annotated
