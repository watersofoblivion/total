import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax
import Total.Stlc.Lang.Annotated.Semantics
import Total.Stlc.Lang.Annotated.Termination

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  namespace Ty
  end Ty

  namespace PrimOp
    namespace Eval₁
      theorem deterministic := sorry
      theorem progress := sorry

      theorem preservesHalting := sorry
      theorem preservesTotality := sorry
    end Eval₁
  end PrimOp

  namespace Term
    namespace Eval₁
      theorem deterministic {τ: Ty} {t t₁ t₂: Term τ}: Eval₁ τ t t₁ → Eval₁ τ t t₂ → t₁ = t₂ := sorry
      theorem progress {τ: Ty} {t₁: Term τ}: IsValue τ t₁ ∨ ∃ t₂: Term τ, Eval₁ τ t₁ t₂ := sorry

      theorem preservesHalting {τ: Ty} {t₁ t₂: Term τ} (he: Eval₁ τ t₁ t₂): Halts t₁ ↔ Halts t₂ := sorry
      theorem preservesTotality {τ: Ty} {t₁ t₂: Term τ} (he: Eval₁ τ t₁ t₂): Total τ t₁ ↔ Total τ t₂ := sorry
    end Eval₁

    namespace Eval
      theorem deterministic {τ: Ty} {t t₁ t₂: Term τ}: Eval₁ τ t t₁ → Eval₁ τ t t₂ → t₁ = t₂ := sorry
      theorem progress {τ: Ty} {t₁: Term τ}: IsValue τ t₁ ∨ ∃ t₂: Term τ, Eval₁ τ t₁ t₂ := sorry

      theorem preservesTotality {τ: Ty} {t₁ t₂: Term τ} (he: Eval τ t₁ t₂): Total τ t₁ ↔ Total τ t₂ := sorry
      theorem normalization {τ: Ty} {t: Term τ}: Halts t := sorry
    end Eval
  end Term

  namespace Top
    namespace Eval₁
      theorem deterministic {τ: Ty} {t t₁ t₂: Top ρ τ}: Eval₁ τ t t₁ → Eval₁ τ t t₂ → t₁ = t₂ := sorry
      theorem progress {τ: Ty} {t₁: Top ρ τ}: IsValue τ t₁ ∨ ∃ t₂: Top ρ τ, Eval₁ τ t₁ t₂ := sorry

      theorem preservesHalting {τ: Ty} {t₁ t₂: Top ρ τ} (he: Eval₁ τ t₁ t₂): Halts t₁ ↔ Halts t₂ := sorry
      theorem preservesTotality {τ: Ty} {t₁ t₂: Top ρ τ} (he: Eval₁ τ t₁ t₂): Total τ t₁ ↔ Total τ t₂ := sorry
    end Eval₁

    namespace Eval
      theorem deterministic {τ: Ty} {t t₁ t₂: Top ρ τ}: Eval₁ τ t t₁ → Eval₁ τ t t₂ → t₁ = t₂ := sorry
      theorem progress {τ: Ty} {t₁: Top ρ τ}: IsValue τ t₁ ∨ ∃ t₂: Top ρ τ, Eval₁ τ t₁ t₂ := sorry

      theorem preservesTotality {τ: Ty} {t₁ t₂: Top ρ τ} (he: Eval τ t₁ t₂): Total τ t₁ ↔ Total τ t₂ := sorry
      theorem normalization {τ: Ty} {t: Top ρ τ}: Halts t := sorry
    end Eval
  end Top
end Total.Stlc.Lang.Annotated
