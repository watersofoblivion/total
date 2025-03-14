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
      theorem deterministic {op: UnOp} {τ₁ τ₂ τ₃ τ₄: Ty}: HasType op τ₁ τ₂ → HasType op τ₃ τ₄ → τ₁ = τ₃ ∧ τ₂ = τ₄
        | .not, .not => ⟨rfl, rfl⟩
    end HasType

    namespace Eval₁
      theorem deterministic {op: UnOp} {t t₁ t₂: Term}: Eval₁ op t t₁ → Eval₁ op t t₂ → t₁ = t₂
        | .not, .not => rfl

      theorem progress {op: UnOp} {τ₁ τ₂: Ty}: {t₁: Term} → HasType op τ₁ τ₂ → ∃ t₂: Term, Eval₁ op t₁ t₂ ∧ Term.IsValue t₂
        | .bool _, .not => ⟨_, ⟨.not, .bool _⟩⟩
        | _, _ => sorry

      theorem preservation {op: UnOp} {τ₁ τ₂: Ty} {t₁ t₂: Term}: HasType op τ₁ τ₂ → Eval₁ op t₁ t₂ → Term.HasType t₂ τ₂
        | .not, .not => .bool
    end Eval₁
  end UnOp

  namespace BinOp
    namespace HasType
      theorem deterministic {op: BinOp} {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆: Ty}: HasType op τ₁ τ₂ τ₃ → HasType op τ₄ τ₅ τ₆ → τ₁ = τ₄ ∧ τ₂ = τ₅ ∧ τ₃ = τ₆
        | .and, .and
        | .or,  .or

        | .add, .add
        | .mul, .mul

        | @HasType.eq .bool,  @HasType.eq  .bool
        | @HasType.eq .nat,   @HasType.eq  .nat
        | @HasType.neq .bool, @HasType.neq .bool
        | @HasType.neq .nat,  @HasType.neq .nat

        | .lt,  .lt
        | .lte, .lte
        | .gt,  .gt
        | .gte, .gte => ⟨rfl, rfl, rfl⟩

        | _, _ => sorry
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

      theorem progress {op: BinOp} {τ₁ τ₂ τ₃: Ty}: {t₁ t₂: Term} → HasType op τ₁ τ₂ τ₃ → ∃ t₃: Term, Eval₁ op t₁ t₂ t₃ ∧ Term.IsValue t₃
        | .bool _, .bool _, .and => ⟨_, .and, .bool _⟩
        | .bool _, .bool _, .or  => ⟨_, .or,  .bool _⟩

        | .nat _, .nat _, .add => ⟨_, .add, .nat _⟩
        | .nat _, .nat _, .mul => ⟨_, .mul, .nat _⟩

        | .bool _, .bool _, .eq  => ⟨_, .eqBool,  .bool _⟩
        | .nat _,  .nat _,  .eq  => ⟨_, .eqNat,   .bool _⟩
        | .bool _, .bool _, .neq => ⟨_, .neqBool, .bool _⟩
        | .nat _,  .nat _,  .neq => ⟨_, .neqNat,  .bool _⟩

        | .nat _, .nat _, .lt  => ⟨_, .lt,  .bool _⟩
        | .nat _, .nat _, .lte => ⟨_, .lte, .bool _⟩
        | .nat _, .nat _, .gt  => ⟨_, .gt,  .bool _⟩
        | .nat _, .nat _, .gte => ⟨_, .gte, .bool _⟩

        | _, _, _ => sorry

      theorem preservation {op: BinOp} {τ₁ τ₂ τ₃: Ty} {t₁ t₂ t₃: Term}: HasType op τ₁ τ₂ τ₃ → Eval₁ op t₁ t₂ t₃ → Term.HasType t₃ τ₃
        | .and, .and
        | .or,  .or  => .bool

        | .add, .add
        | .mul, .mul => .nat

        | .eq,  .eqBool
        | .eq,  .eqNat
        | .neq, .neqBool
        | .neq, .neqNat => .bool

        | .lt,  .lt
        | .lte, .lte
        | .gt,  .gt
        | .gte, .gte => .bool
    end Eval₁
  end BinOp

  namespace Term
    namespace HasType
      theorem deterministic {t: Term} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂
        | .bool,          .bool
        | .nat,           .nat           => rfl
        | .unOp  op₁ _,   .unOp  op₂ _   => (UnOp.HasType.deterministic op₁ op₂).right
        | .binOp op₁ _ _, .binOp op₂ _ _ => (BinOp.HasType.deterministic op₁ op₂).right.right
        | .cond _ t₁ _,   .cond _ t₂ _   => by rw [deterministic t₁ t₂]
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Term}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂
        | .unOp _ e₁, .unOp _ e₂ => by rw [UnOp.Eval₁.deterministic e₁ e₂]
        | .unOpOp e₁, .unOpOp e₂ => by rw [deterministic e₁ e₂]

        | .binOp    _ _ e₁, .binOp    _ _ e₂ => by rw [BinOp.Eval₁.deterministic e₁ e₂]
        | .binOpRight _ e₁, .binOpRight _ e₂
        | .binOpLeft    e₁, .binOpLeft    e₂ => by rw [deterministic e₁ e₂]

        | .condTrue,  .condTrue
        | .condFalse, .condFalse => rfl
        | .cond e₁,   .cond e₂   => by rw [deterministic e₁ e₂]

        | _, _ => sorry

      theorem preservation {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ
        | .unOp op _,       .unOp _ e => UnOp.Eval₁.preservation op e
        | .unOp op operand, .unOpOp e => .unOp op (preservation operand e)

        | .binOp op _ _,     .binOp    _ _ e => BinOp.Eval₁.preservation op e
        | .binOp op lhs rhs, .binOpRight _ e => .binOp op lhs (preservation rhs e)
        | .binOp op lhs rhs, .binOpLeft    e => .binOp op (preservation lhs e) rhs

        | .cond _ t _, .condTrue  => t
        | .cond _ _ f, .condFalse => f
        | .cond c t f, .cond e    => .cond (preservation c e) t f

      theorem progress {τ: Ty} {t₁: Term}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂
        | .bool => .inl (.bool _)
        | .nat  => .inl (.nat  _)

        | .unOp op operand =>
          match UnOp.Eval₁.progress op, progress operand with
            | ⟨_, e, _⟩, .inl v      => .inr ⟨_, .unOp v e⟩
            | ⟨_, _, _⟩, .inr ⟨_, e⟩ => .inr ⟨_, .unOpOp e⟩

        | .binOp op lhs rhs =>
          match BinOp.Eval₁.progress op, progress lhs, progress rhs with
            | ⟨_, e, _⟩, .inl v₁,      .inl v₂     => .inr ⟨_, .binOp v₁ v₂ e⟩
            | _,         .inl v,       .inr ⟨_, e⟩ => .inr ⟨_, .binOpRight v e⟩
            | _,         .inr ⟨_, e⟩,  _           => .inr ⟨_, .binOpLeft e⟩

        | .cond c t f =>
          match progress c with
            | .inl (.bool true)  => .inr ⟨_, .condTrue⟩
            | .inl (.bool false) => .inr ⟨_, .condFalse⟩
            | .inr ⟨_, e⟩        => .inr ⟨_, .cond e⟩

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

        | .unOp op operand, .refl => .unOp op (preservation operand .refl)
        | .unOp op _, .trans (.unOp _ operand) hyz => sorry
        | .unOp op _, .trans (.unOpOp he)      hyz => sorry

        | .binOp op lhs rhs, .refl                       => .binOp op (preservation lhs .refl) (preservation rhs .refl)
        | .binOp op lhs rhs, .trans (.binOp o l r) .refl =>
          have ih := BinOp.Eval₁.preservation op _
          have ih₁ := preservation lhs .refl
          have ih₂ := preservation rhs .refl
          .binOp ih ih₁ ih₂
        | .binOp op lhs rhs, .trans (.binOpRight hv he) hyz   =>
          have h := BinOp.Eval₁.preservation op _
          have ih := preservation (Eval₁.preservation rhs he) (.trans he hyz)
          sorry
        | .binOp op lhs rhs, .trans (.binOpLeft he)     hyz   =>
          have h := BinOp.Eval₁.preservation op _
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
          match UnOp.Eval₁.progress op, progress operand with
            | ⟨_, e, v⟩, .inl (.bool _)           => .inr ⟨_, .trans (.unOp (.bool _) e) .refl⟩
            | ⟨_, e, v⟩, .inr ⟨_, .refl⟩          => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩
            | ⟨_, e, v⟩, .inr ⟨_, .trans hxy hyz⟩ => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩

        | .binOp op lhs rhs =>
          match BinOp.Eval₁.progress op, progress lhs, progress rhs with
            | ⟨_, e, v⟩, .inl (.bool _),           .inl (.bool _)           => .inr ⟨_, .trans (.binOp op) .refl⟩
            | ⟨_, e, v⟩, .inl hv,                  .inr ⟨_, .refl⟩          => sorry -- .inr ⟨_, .trans (.andRight hv _) .refl⟩
            | ⟨_, e, v⟩, .inl hv,                  .inr ⟨_, .trans hxy hyz⟩ => sorry -- .inr ⟨_, .trans (.andRight hv hxy) hyz⟩
            | ⟨_, e, v⟩, .inr ⟨_, .refl⟩,          _                        => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩
            | ⟨_, e, v⟩, .inr ⟨_, .trans hxy hyz⟩, _                        => sorry -- .inr ⟨_, .trans (.andLeft _) .refl⟩

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
