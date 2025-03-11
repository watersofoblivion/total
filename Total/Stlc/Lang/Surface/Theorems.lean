import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax
import Total.Stlc.Lang.Surface.Semantics

namespace Total.Stlc.Lang.Surface
  namespace Ty
  end Ty

  namespace Term
    namespace HasType
      theorem deterministic {ε: Env} {t: Term} {τ₁ τ₂: Ty}: HasType ε t τ₁ → HasType ε t τ₂ → τ₁ = τ₂ := sorry
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Term}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂ := sorry
      theorem preservation {ε: Env} {τ: Ty} {t₁ t₂: Term}: HasType ε t₁ τ → Eval₁ t₁ t₂ → HasType ε t₂ τ := sorry
      theorem progress {ε: Env} {τ: Ty} {t₁: Term}: HasType ε t₁ τ → IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry

      -- TODO: Theorems for Strong Normalization
      theorem confluent {ε: Env} {τ: Ty} {t₁ t₂ t₃: Term}: Eval₁ t₁ t₂ → Eval₁ t₁ t₃ → ∃ t₄: Term, Eval₁ t₂ t₄ ∧ Eval₁ t₃ t₄ := sorry
      theorem strongly_normalizing {ε: Env} {τ: Ty} {t₁: Term}: IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
    end Eval₁
  end Term

  namespace Top
    namespace HasType
      theorem deterministic {t: Top} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂ := sorry
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Top}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂ := sorry
      theorem preservation {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ := sorry
      theorem progress {τ: Ty} {t₁: Top}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Top, Eval₁ t₁ t₂ := sorry
    end Eval₁
  end Top
end Total.Stlc.Lang.Surface
