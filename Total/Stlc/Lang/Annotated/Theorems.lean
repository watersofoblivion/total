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
      theorem deterministic {α: Nat} {δ: Domain α} {τ: Ty} {op: PrimOp δ τ} {args: Values δ} {t₁ t₂: Term τ}: Eval₁ op args t₁ → Eval₁ op args t₂ → t₁ = t₂
        | .and _, .and _
        | .or  _, .or  _
        | .not _, .not _

        | .add _, .add _
        | .mul _, .mul _

        | .eqBool  _, .eqBool  _
        | .eqNat   _, .eqNat   _
        | .neqBool _, .neqBool _
        | .neqNat  _, .neqNat  _

        | .lt  _, .lt  _
        | .lte _, .lte _
        | .gt  _, .gt  _
        | .gte _, .gte _ => rfl

      theorem progress {α: Nat} {δ: Domain α} {τ: Ty}: (op: PrimOp δ τ) → (args: Values δ) → ∃ t: Term τ, Eval₁ op args t ∧ Term.IsValue t
        | .and, .cons (.bool lhs) (.nil (.bool rhs)) => ⟨_, .and (.cons (.bool lhs) (.nil (.bool rhs))), .value (.bool _)⟩
        | .or , .cons (.bool lhs) (.nil (.bool rhs)) => ⟨_, .or  (.cons (.bool lhs) (.nil (.bool rhs))), .value (.bool _)⟩
        | .not, .nil  (.bool op)                     => ⟨_, .not (.nil (.bool op)), .value (.bool _)⟩

        | .add, .cons (.nat lhs) (.nil (.nat rhs)) => ⟨_, .add (.cons (.nat lhs) (.nil (.nat rhs))), .value (.nat _)⟩
        | .mul, .cons (.nat lhs) (.nil (.nat rhs)) => ⟨_, .mul (.cons (.nat lhs) (.nil (.nat rhs))), .value (.nat _)⟩

        | .eq,  .cons (.bool lhs) (.nil (.bool rhs)) => ⟨_, .eqBool  (.cons (.bool lhs) (.nil (.bool rhs))), .value (.bool _)⟩
        | .eq,  .cons (.nat  lhs) (.nil (.nat  rhs)) => ⟨_, .eqNat   (.cons (.nat  lhs) (.nil (.nat  rhs))), .value (.bool _)⟩
        | .neq, .cons (.bool lhs) (.nil (.bool rhs)) => ⟨_, .neqBool (.cons (.bool lhs) (.nil (.bool rhs))), .value (.bool _)⟩
        | .neq, .cons (.nat  lhs) (.nil (.nat  rhs)) => ⟨_, .neqNat  (.cons (.nat  lhs) (.nil (.nat  rhs))), .value (.bool _)⟩

        | .lt , .cons (.nat lhs) (.nil (.nat rhs)) => ⟨_, .lt  (.cons (.nat lhs) (.nil (.nat rhs))), .value (.bool _)⟩
        | .lte, .cons (.nat lhs) (.nil (.nat rhs)) => ⟨_, .lte (.cons (.nat lhs) (.nil (.nat rhs))), .value (.bool _)⟩
        | .gt , .cons (.nat lhs) (.nil (.nat rhs)) => ⟨_, .gt  (.cons (.nat lhs) (.nil (.nat rhs))), .value (.bool _)⟩
        | .gte, .cons (.nat lhs) (.nil (.nat rhs)) => ⟨_, .gte (.cons (.nat lhs) (.nil (.nat rhs))), .value (.bool _)⟩

      theorem preservesHalting: True := .intro
      theorem preservesTotality: True := .intro
    end Eval₁
  end PrimOp

  mutual
    theorem Term.Eval₁.deterministic {τ: Ty} {t t₁ t₂: Term τ}: Term.Eval₁ t t₁ → Term.Eval₁ t t₂ → t₁ = t₂ := sorry
    theorem Args.Eval₁.deterministic {α: Nat} {δ: Domain α} {a a₁ a₂: Args δ}: Args.Eval₁ a a₁ → Args.Eval₁ a a₂ → a₁ = a₂ := sorry
  end

  mutual
    theorem Term.Eval₁.progress {τ: Ty}: (t₁: Term τ) → Term.IsValue t₁ ∨ ∃ t₂: Term τ, Term.Eval₁ t₁ t₂ := sorry
    theorem Args.Eval₁.progress {α: Nat} {δ: Domain α}: (a₁: Args δ) → Args.IsValue a₁ ∨ ∃ a₂: Args δ, Args.Eval₁ a₁ a₂ := sorry
  end

  mutual
    theorem Term.Eval₁.preservesHalting {τ: Ty} {t₁ t₂: Term τ} (he: Term.Eval₁ t₁ t₂): Term.Halts t₁ ↔ Term.Halts t₂ := sorry
    theorem Args.Eval₁.preservesHalting {α: Nat} {δ: Domain α} {a₁ a₂: Args δ} (he: Args.Eval₁ a₁ a₂): Args.Halts a₁ ↔ Args.Halts a₂ := sorry
  end

  mutual
    theorem Term.Eval₁.preservesTotality {τ: Ty} {t₁ t₂: Term τ} (he: Term.Eval₁ t₁ t₂): Term.Total t₁ ↔ Term.Total t₂ := sorry
    theorem Args.Eval₁.preservesTotality {α: Nat} {δ: Domain α} {a₁ a₂: Args δ} (he: Args.Eval₁ a₁ a₂): Args.Total a₁ ↔ Args.Total a₂ := sorry
  end

  namespace Term
    namespace Eval
      theorem progress {τ: Ty} {t₁: Term τ}: IsValue t₁ ∨ ∃ t₂: Term τ, Eval₁ t₁ t₂ := sorry

      theorem preservesTotality {τ: Ty} {t₁ t₂: Term τ} (he: Eval t₁ t₂): Total t₁ ↔ Total t₂ := sorry
      theorem normalization {τ: Ty} {t: Term τ}: Halts t := sorry
    end Eval
  end Term

  namespace Top
    namespace Eval₁
      theorem deterministic {τ: Ty} {t t₁ t₂: Top τ}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂ := sorry
      theorem progress {τ: Ty} {t₁: Top τ}: IsValue t₁ ∨ ∃ t₂: Top τ, Eval₁ t₁ t₂ := sorry

      theorem preservesHalting {τ: Ty} {t₁ t₂: Top τ} (he: Eval₁ t₁ t₂): Halts t₁ ↔ Halts t₂ := sorry
      theorem preservesTotality {τ: Ty} {t₁ t₂: Top τ} (he: Eval₁ t₁ t₂): Total τ t₁ ↔ Total τ t₂ := sorry
    end Eval₁

    namespace Eval
      theorem progress {τ: Ty} {t₁: Top τ}: IsValue t₁ ∨ ∃ t₂: Top τ, Eval t₁ t₂ := sorry

      theorem preservesTotality {τ: Ty} {t₁ t₂: Top τ} (he: Eval t₁ t₂): Total τ t₁ ↔ Total τ t₂ := sorry
      theorem normalization {τ: Ty} {t: Top τ}: Halts t := sorry
    end Eval
  end Top
end Total.Stlc.Lang.Annotated
