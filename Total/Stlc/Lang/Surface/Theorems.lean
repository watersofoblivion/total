import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax
import Total.Stlc.Lang.Surface.Semantics

namespace Total.Stlc.Lang.Surface
  set_option maxHeartbeats 10000000
  namespace Ty
  end Ty

  namespace UnOp
    namespace HasType
      theorem deterministic {op: UnOp} {τ₁ τ₂ τ₃: Ty}: HasType op τ₁ τ₂ → HasType op τ₁ τ₃ → τ₂ = τ₃
        | .not, .not => rfl
    end HasType

    namespace Eval₁
      theorem deterministic {op: UnOp} {t t₁ t₂: Term}: Eval₁ op t t₁ → Eval₁ op t t₂ → t₁ = t₂
        | .not, .not => rfl

      theorem progress {op: UnOp} {τ₁ τ₂: Ty} {t₁: Term}: HasType op τ₁ τ₂ → ∃ t₂: Term, Eval₁ op t₁ t₂
        | .not => ⟨_, .not⟩

      theorem preservation {op: UnOp} {τ₁ τ₂: Ty} {t₁ t₂: Term}: HasType op τ₁ τ₂ → Eval₁ op t₁ t₂ → Term.HasType t₂ τ₂
        | .not, .not => rfl
    end Eval₁
  end UnOp

  namespace BinOp
    namespace HasType
      theorem deterministic {op: BinOp} {τ₁ τ₂ τ₃ τ₄: Ty}: HasType op τ₁ τ₂ τ₃ → HasType op τ₁ τ₂ τ₄ → τ₃ = τ₄
        | .and, .and
        | .or,  .or

        | .add, .add
        | .mul, .mul

        | .eq,  .eq
        | .neq, .neq

        | .lt,  .lt
        | .lte, .lte
        | .gt,  .gt
        | .gte, .gte => rfl
    end HasType

    namespace Eval₁
      theorem deterministic {op: BinOp} {t₁ t₂ t₃ t₄: Term}: Eval₁ op t₁ t₂ t₃ → Eval₁ op t₁ t₂ t₄ → t₃ = t₄
        | .and, .and
        | .or,  .or

        | .add, .add
        | .mul, .mul

        | .eqBool,  .eqBool
        | .eqNat,   .eqNat
        | .neqBool, .neqBool
        | .neqNat,  .neqNat

        | .lt,  .lt
        | .lte, .lte
        | .gt,  .gt
        | .gte, .gte => rfl

      theorem progress {op: BinOp} {τ₁ τ₂ τ₃: Ty} {t₁ t₂: Term}: HasType op τ₁ τ₂ τ₃ → ∃ t₃: Term, Eval₁ op t₁ t₂ t₃ := sorry
      theorem preservation {op: BinOp} {τ₁ τ₂ τ₃: Ty} {t₁ t₂ t₃: Term}: HasType op τ₁ τ₂ τ₃ → Eval₁ op t₁ t₂ t₃ → Term.HasType t₂ τ₃ := sorry
    end Eval₁
  end BinOp

  namespace Term
    namespace HasType
      theorem deterministic {t: Term} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂
        | .bool,          .bool
        | .nat,           .nat           => rfl
        | .unOp  op₁ _,   .unOp  op₂ _   => UnOp.HasType.deterministic op₁ op₂
        | .binOp op₁ _ _, .binOp op₂ _ _ => BinOp.HasType.deterministic op₁ op₂
        | .cond _ t₁ _,   .cond _ t₂ _   => by rw [deterministic t₁ t₂]
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Term}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂
        | .unOp _ he₁, .unOp _ he₂ => by rw [UnOp.Eval₁.deterministic he₁ he₂]
        | .unOpOp he₁, .unOpOp he₂ => by rw [deterministic he₁ he₂]

        | .binOp    _ _ he₁, .binOp    _ _ he₂ => by rw [BinOp.Eval₁.deterministic he₁ he₂]
        | .binOpRight _ he₁, .binOpRight _ he₂
        | .binOpLeft    he₁, .binOpLeft    he₂ => by rw [deterministic he₁ he₂]

        | .condTrue,  .condTrue
        | .condFalse, .condFalse => rfl
        | .cond he₁,  .cond he₂  => by rw [deterministic he₁ he₂]

      theorem preservation {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ
        | .unOp ht _,  .unOp      => UnOp.Eval₁.preservation ht
        | .unOp ht op, .unOpOp he => preservation op he

        | .binOp ht _ _,   .binOp => BinOp.Eval₁.preservation ht
        | .binOp lhs rhs, .binOpRight _ he => .add lhs (preservation rhs he)
        | .binOp lhs rhs, .binOpLeft    he => .add (preservation lhs he) rhs

        | .cond _ t _, .condTrue  => t
        | .cond _ _ f, .condFalse => f
        | .cond c t f, .cond   he => .cond (preservation c he) t f

      theorem progress {τ: Ty} {t₁: Term}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂
        | .bool => .inl (.bool _)
        | .nat  => .inl (.nat  _)

        | .unOp op operand =>
          match progress operand with
            | .inl v       => .inr ⟨_, .unOp v⟩
            | .inr ⟨_, he⟩ => .inr ⟨_, .notOp he⟩

        | .binOp op lhs rhs =>
          match progress lhs, progress rhs with
            | .inl hv₁, .inl hv₂ => .inr ⟨_, .binOp hv₁ hv₂ (UnOp.Eval₁ op hv₁ hv₂)⟩
            | .inl hv,       .inr ⟨_, he⟩  => .inr ⟨_, .binOpRight hv he⟩
            | .inr ⟨_, he⟩,  _             => .inr ⟨_, .binOpLeft he⟩

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
      theorem deterministic {t t₁ t₂: Term}: Eval t t₁ → Eval t t₂ → t₁ = t₂
        | .refl,            .refl            => rfl
        | .refl,            .trans hxy  hyz  => by sorry
        | .trans hxy  hyz,  .refl            => by sorry
        | .trans hxy₁ hyz₁, .trans hxy₂ hyz₂ => by sorry
          -- have h₁ := Eval₁.deterministic hxy₁ hxy₂
          -- have h₂ := Eval.deterministic hyz₁ hyz₂
          -- by
          --   sorry

      theorem preservation {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval t₁ t₂ → HasType t₂ τ
        | .bool, .refl          => .bool
        | .bool, .trans hxy hyz => sorry

        | .nat, .refl          => .nat
        | .nat, .trans hxy hyz => sorry


        | .unOp op, .refl => .unOp (preservation op .refl)
        -- | .unOp op, .trans .not        hyz => sorry
        -- | .unOp op, .trans (.unOpOp he) hyz => sorry

        | .binOp lhs rhs, .refl               => .binOp (preservation lhs .refl) (preservation rhs .refl)
        | .binOp lhs rhs, .trans .binOp .refl =>
          have ih₁ := preservation lhs .refl
          have ih₂ := preservation rhs .refl
          sorry
        | .binOp lhs rhs, .trans (.binOpRight hv he) hyz   =>
          have ih := preservation (Eval₁.preservation rhs he) (.trans he hyz)
          sorry
        | .binOp lhs rhs, .trans (.binOpLeft he)     hyz   =>
          have ih := preservation (Eval₁.preservation lhs he) (.trans he hyz)
          sorry

        -- | .cond c t f, .refl                 => .cond (preservation c .refl) (preservation t .refl) (preservation f .refl)
        -- | .cond c t f, .trans .condTrue  hyz => sorry
        -- | .cond c t f, .trans (@Eval₁.condFalse .(t₁) .(t₂)) hyz => sorry
        -- | .cond c t f, .trans (.cond he) hyz => sorry

        | _, _ => sorry

      theorem progress {τ: Ty} {t₁: Term}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Term, Eval t₁ t₂
        | .bool => .inl (.bool _)
        | .nat  => .inl (.nat  _)

        | .unOp op operand =>
          match progress operand with
            | .inl (.bool _)           => .inr ⟨_, .trans (.unOp op) .refl⟩
            | .inl hv                  => sorry -- .inr ⟨_, .trans (.andRight hv _) .refl⟩
            | .inr ⟨_, .refl⟩          => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩
            | .inr ⟨_, .trans hxy hyz⟩ => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩

        | .binOp op lhs rhs =>
          match progress lhs, progress rhs with
            | .inl (.bool _),           .inl (.bool _)           => .inr ⟨_, .trans (.binOp op) .refl⟩
            | .inl hv,                  .inr ⟨_, .refl⟩          => sorry -- .inr ⟨_, .trans (.andRight hv _) .refl⟩
            | .inl hv,                  .inr ⟨_, .trans hxy hyz⟩ => sorry -- .inr ⟨_, .trans (.andRight hv hxy) hyz⟩
            | .inr ⟨_, .refl⟩,          _                        => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩
            | .inr ⟨_, .trans hxy hyz⟩, _                        => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩

        | .cond c t f =>
          match progress c with
            | .inl hv      => sorry
            | .inr ⟨_, he⟩ => sorry
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
