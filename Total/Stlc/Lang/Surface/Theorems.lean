import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax
import Total.Stlc.Lang.Surface.Semantics

namespace Total.Stlc.Lang.Surface
  namespace Ty
  end Ty

  namespace Term
    namespace HasType
      theorem deterministic {t: Term} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂
        | .bool, .bool
        | .nat,  .nat  => rfl

        | .and _ _, .and _ _
        | .or  _ _, .or  _ _
        | .not _,   .not _   => rfl

        | .add _ _, .add _ _
        | .mul _ _, .mul _ _ => rfl

        | .eq  _ _, .eq  _ _
        | .neq _ _, .neq _ _ => rfl

        | .lt  _ _, .lt  _ _
        | .lte _ _, .lte _ _
        | .gt  _ _, .gt  _ _
        | .gte _ _, .gte _ _ => rfl

        | .cond _ t₁ _, .cond _ t₂ _ =>
          have ih₂ := deterministic t₁ t₂
          by rw [ih₂]

        | .lt  _ _, .gt  _ _
        | .lte _ _, .gte _ _
        | .gt  _ _, .lt  _ _
        | .gte _ _, .lte _ _ => rfl
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Term}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂ := sorry
      theorem preservation {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ := sorry
      theorem progress {τ: Ty} {t₁: Term}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry

      -- TODO: Theorems for Strong Normalization
      theorem confluent {τ: Ty} {t₁ t₂ t₃: Term}: Eval₁ t₁ t₂ → Eval₁ t₁ t₃ → ∃ t₄: Term, Eval₁ t₂ t₄ ∧ Eval₁ t₃ t₄ := sorry
      theorem strongly_normalizing {τ: Ty} {t₁: Term}: IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
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
