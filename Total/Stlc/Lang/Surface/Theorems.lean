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
    end HasType

    namespace Eval₁
      set_option maxHeartbeats 1000000

      theorem deterministic {t t₁ t₂: Term}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂
        | .and, .and
        | .or,  .or
        | .not, .not

        | .add, .add
        | .mul, .mul

        | .eqBool,  .eqBool
        | .eqNat,   .eqNat
        | .neqBool, .neqBool
        | .neqNat,  .neqNat

        | .lt,  .lt
        | .lte, .lte
        | .gt,  .gt
        | .gte, .gte

        | .condTrue,  .condTrue
        | .condFalse, .condFalse => rfl

        | .andRight _ he₁, .andRight _ he₂
        | .andLeft    he₁, .andLeft    he₂
        | .orRight  _ he₁, .orRight  _ he₂
        | .orLeft     he₁, .orLeft     he₂
        | .notOp      he₁, .notOp      he₂

        | .addRight _ he₁, .addRight _ he₂
        | .addLeft    he₁, .addLeft    he₂
        | .mulRight _ he₁, .mulRight _ he₂
        | .mulLeft    he₁, .mulLeft    he₂

        | .eqRight  _ he₁, .eqRight  _ he₂
        | .eqLeft     he₁, .eqLeft     he₂
        | .neqRight _ he₁, .neqRight _ he₂
        | .neqLeft    he₁, .neqLeft    he₂

        | .gtRight  _ he₁, .gtRight  _ he₂
        | .gtLeft     he₁, .gtLeft     he₂
        | .gteRight _ he₁, .gteRight _ he₂
        | .gteLeft    he₁, .gteLeft    he₂
        | .ltRight  _ he₁, .ltRight  _ he₂
        | .ltLeft     he₁, .ltLeft     he₂
        | .lteRight _ he₁, .lteRight _ he₂
        | .lteLeft    he₁, .lteLeft    he₂

        | .cond       he₁, .cond       he₂ =>
          have ih := deterministic he₁ he₂
          by rw [ih]

        | .gteRight hv he₁, .gteLeft he₂ => sorry
        | .gtRight  _ _, .gtLeft  _
        | .lteRight _ _, .lteLeft _
        | .ltRight  _ _, .ltLeft  _
        | .neqRight _ _, .neqLeft _
        | .eqRight  _ _, .eqLeft  _
        | .mulRight _ _, .mulLeft _
        | .addRight _ _, .addLeft _
        | .orRight  _ _, .orLeft  _
        | .andRight _ _, .andLeft _ => sorry

      theorem preservation {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ
        | .and _   _,   .and           => .bool
        | .and lhs rhs, .andRight _ he => .and lhs (preservation rhs he)
        | .and lhs rhs, .andLeft    he => .and (preservation lhs he) rhs

        | .or _   _,   .or           => .bool
        | .or lhs rhs, .orRight _ he => .or lhs (preservation rhs he)
        | .or lhs rhs, .orLeft    he => .or (preservation lhs he) rhs

        | .not _,  .not      => .bool
        | .not op, .notOp he => preservation op he

        | .add _   _,   .add           => .nat
        | .add lhs rhs, .addRight _ he => .add lhs (preservation rhs he)
        | .add lhs rhs, .addLeft    he => .add (preservation lhs he) rhs

        | .mul _   _,   .mul           => .nat
        | .mul lhs rhs, .mulRight _ he => .mul lhs (preservation rhs he)
        | .mul lhs rhs, .mulLeft    he => .mul (preservation lhs he) rhs

        | .eq _   _,   .eqBool       => .bool
        | .eq _   _,   .eqNat        => .bool
        | .eq lhs rhs, .eqRight _ he => .eq lhs (preservation rhs he)
        | .eq lhs rhs, .eqLeft    he => .eq (preservation lhs he) rhs

        | .neq _   _,   .neqBool       => .bool
        | .neq _   _,   .neqNat        => .bool
        | .neq lhs rhs, .neqRight _ he => .neq lhs (preservation rhs he)
        | .neq lhs rhs, .neqLeft    he => .neq (preservation lhs he) rhs

        | .lt _   _,   .lt           => .bool
        | .lt lhs rhs, .ltRight _ he => .lt  lhs (preservation rhs he)
        | .lt lhs rhs, .ltLeft    he => .lt  (preservation lhs he) rhs

        | .lte _   _,    .lte          => .bool
        | .lte lhs rhs, .lteRight _ he => .lte lhs (preservation rhs he)
        | .lte lhs rhs, .lteLeft    he => .lte (preservation lhs he) rhs

        | .gt _   _,   .gt           => .bool
        | .gt lhs rhs, .gtRight _ he => .gt  lhs (preservation rhs he)
        | .gt lhs rhs, .gtLeft    he => .gt  (preservation lhs he) rhs

        | .gte _   _,   .gte           => .bool
        | .gte lhs rhs, .gteRight _ he => .gte lhs (preservation rhs he)
        | .gte lhs rhs, .gteLeft    he => .gte (preservation lhs he) rhs

        | .cond _ t _, .condTrue  => t
        | .cond _ _ f, .condFalse => f
        | .cond c t f, .cond   he => .cond (preservation c he) t f

      theorem progress {τ: Ty} {t₁: Term}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂
        | .bool => .inl (.bool _)
        | .nat  => .inl (.nat  _)

        | .and lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.bool _), .inl (.bool _) => .inr ⟨_, .and⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .andRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .andLeft he⟩
        | .or  lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.bool _), .inl (.bool _) => .inr ⟨_, .or⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .orRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .orLeft he⟩
        | .not op =>
          match progress op with
            | .inl (.bool _) => .inr ⟨_, .not⟩
            | .inr ⟨_, he⟩   => .inr ⟨_, .notOp he⟩

        | .add lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.nat _), .inl (.nat _) => .inr ⟨_, .add⟩
            | .inl hv,       .inr ⟨_, he⟩  => .inr ⟨_, .addRight hv he⟩
            | .inr ⟨_, he⟩,  _             => .inr ⟨_, .addLeft he⟩
        | .mul lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.nat _), .inl (.nat _) => .inr ⟨_, .mul⟩
            | .inl hv,       .inr ⟨_, he⟩  => .inr ⟨_, .mulRight hv he⟩
            | .inr ⟨_, he⟩,  _             => .inr ⟨_, .mulLeft he⟩

        | .eq  lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.bool _), .inl (.bool _) => .inr ⟨_, .eqBool⟩
            | .inl (.nat _),  .inl (.nat _)  => .inr ⟨_, .eqNat⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .eqRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .eqLeft he⟩

            | .inl (.nat _),  .inl (.bool true)  => sorry
            | .inl (.nat _),  .inl (.bool false) => sorry
            | .inl (.bool _), .inl (.nat _)      => sorry
        | .neq lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.bool _), .inl (.bool _) => .inr ⟨_, .neqBool⟩
            | .inl (.nat _),  .inl (.nat _)  => .inr ⟨_, .neqNat⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .neqRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .neqLeft he⟩

            | .inl (.nat _),  .inl (.bool true)  => sorry
            | .inl (.nat _),  .inl (.bool false) => sorry
            | .inl (.bool _), .inl (.nat _)      => sorry

        | .lt  lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.nat _),  .inl (.nat _)  => .inr ⟨_, .lt⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .ltRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .ltLeft he⟩
        | .lte lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.nat _),  .inl (.nat _)  => .inr ⟨_, .lte⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .lteRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .lteLeft he⟩
        | .gt  lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.nat _),  .inl (.nat _)  => .inr ⟨_, .gt⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .gtRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .gtLeft he⟩
        | .gte lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.nat _),  .inl (.nat _)  => .inr ⟨_, .gte⟩
            | .inl hv,        .inr ⟨_, he⟩   => .inr ⟨_, .gteRight hv he⟩
            | .inr ⟨_, he⟩,   _              => .inr ⟨_, .gteLeft he⟩

        | .cond c t f =>
          match progress c with
            | .inl (.bool true)  => .inr ⟨_, .condTrue⟩
            | .inl (.bool false) => .inr ⟨_, .condFalse⟩
            | .inr ⟨_, he⟩       => .inr ⟨_, .cond he⟩

      -- TODO: Theorems for Strong Normalization
      theorem confluent {τ: Ty} {t₁ t₂ t₃: Term}: Eval₁ t₁ t₂ → Eval₁ t₁ t₃ → ∃ t₄: Term, Eval₁ t₂ t₄ ∧ Eval₁ t₃ t₄ := sorry
      theorem strongly_normalizing {τ: Ty} {t₁: Term}: IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
    end Eval₁

    namespace Eval
      theorem deterministic {t t₁ t₂: Term}: Eval t t₁ → Eval t t₂ → t₁ = t₂ := sorry
      theorem preservation {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval t₁ t₂ → HasType t₂ τ := sorry
      theorem progress {τ: Ty} {t₁: Term}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Term, Eval t₁ t₂ := sorry
    end Eval
  end Term

  namespace Top
    namespace HasType
      theorem deterministic {t: Top} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂
        | h, _ => nomatch h
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Top}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂
        | h, _ => nomatch h

      theorem preservation {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ
        | h, _ => nomatch h

      theorem progress {τ: Ty} {t₁: Top}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Top, Eval₁ t₁ t₂
        | h => nomatch h
    end Eval₁

    namespace Eval
      theorem deterministic {t t₁ t₂: Top}: Eval t t₁ → Eval t t₂ → t₁ = t₂
        | h, _ => nomatch h

      theorem preservation {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval t₁ t₂ → HasType t₂ τ
        | h, _ => nomatch h

      theorem progress {τ: Ty} {t₁: Top}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Top, Eval t₁ t₂
        | h => nomatch h
    end Eval
  end Top
end Total.Stlc.Lang.Surface
