import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax
import Total.Stlc.Lang.Surface.Semantics

namespace Total.Stlc.Lang.Surface
  set_option maxHeartbeats 10000000

  namespace Ty
  end Ty

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

      theorem preservesTyping {op: UnOp} {τ₁ τ₂: Ty} {t₁ t₂: Term}: HasType op τ₁ τ₂ → Eval₁ op t₁ t₂ → Term.HasType t₂ τ₂
        | .not, .not => .bool

      -- theorem preservesHalting {t₁ t₂: Term} (he: Eval₁ t₁ t₂): Halts t₁ ↔ Halts t₂ :=

      theorem preservesHalting {op: UnOp} {t₁ t₂: Term} (he: Eval₁ op t₁ t₂): Halts op t₁ ↔ Halts op t₂ :=
        ⟨mp he, mpr he⟩
        where
          mp  {op: UnOp} {t₁ t₂: Term} (he: Eval₁ op t₁ t₂): Halts op t₁ → Halts op t₂ := sorry
          mpr {op: UnOp} {t₁ t₂: Term} (he: Eval₁ op t₁ t₂): Halts op t₂ → Halts op t₁ := sorry

      theorem preservesTotality {τ₁ τ₂: Ty} {op: UnOp} {t₁ t₂: Term} (ht: HasType op τ₁ τ₂) (he: Eval₁ op t₁ t₂): Total τ₁ τ₂ op t₁ ↔ Total τ₁ τ₂ op t₂ :=
        ⟨mp ht he, mpr ht he⟩
        where
          mp  {τ₁ τ₂: Ty} {op: UnOp} {t₁ t₂: Term} (ht: HasType op τ₁ τ₂) (he: Eval₁ op t₁ t₂): Total τ₁ τ₂ op t₁ → Total τ₁ τ₂ op t₂ := sorry
          mpr {τ₁ τ₂: Ty} {op: UnOp} {t₁ t₂: Term} (ht: HasType op τ₁ τ₂) (he: Eval₁ op t₁ t₂): Total τ₁ τ₂ op t₂ → Total τ₁ τ₂ op t₁ := sorry
    end Eval₁
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

      theorem preservesTyping {op: BinOp} {τ₁ τ₂ τ₃: Ty} {t₁ t₂ t₃: Term}: HasType op τ₁ τ₂ τ₃ → Eval₁ op t₁ t₂ t₃ → Term.HasType t₃ τ₃
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

      theorem preservesHalting {op: BinOp} {t₁ t₂ t₃: Term} (he: Eval₁ op t₁ t₂ t₃): Halts op t₁ t₂ ↔ Halts op t₁ t₂ :=
        ⟨mp he, mpr he⟩
        where
          mp  {op: BinOp} {t₁ t₂ t₃: Term} (he: Eval₁ op t₁ t₂ t₃): Halts op t₁ t₂ → Halts op t₁ t₂ := sorry
          mpr {op: BinOp} {t₁ t₂ t₃: Term} (he: Eval₁ op t₁ t₂ t₃): Halts op t₁ t₂ → Halts op t₁ t₂ := sorry

      theorem preservesTotality {τ₁ τ₂ τ₃: Ty} {op: BinOp} {t₁ t₂ t₃: Term} (ht: HasType op τ₁ τ₂ τ₃) (he: Eval₁ op t₁ t₂ t₃): Total τ₁ τ₂ τ₃ op t₁ t₂ ↔ Total τ₁ τ₂ τ₃ op t₁ t₂ :=
        ⟨mp ht he, mpr ht he⟩
        where
          mp  {τ₁ τ₂ τ₃: Ty} {op: BinOp} {t₁ t₂ t₃: Term} (ht: HasType op τ₁ τ₂ τ₃) (he: Eval₁ op t₁ t₂ t₃): Total τ₁ τ₂ τ₃ op t₁ t₂ → Total τ₁ τ₂ τ₃ op t₁ t₂ := sorry
          mpr {τ₁ τ₂ τ₃: Ty} {op: BinOp} {t₁ t₂ t₃: Term} (ht: HasType op τ₁ τ₂ τ₃) (he: Eval₁ op t₁ t₂ t₃): Total τ₁ τ₂ τ₃ op t₁ t₂ → Total τ₁ τ₂ τ₃ op t₁ t₂ := sorry
    end Eval₁
  end BinOp

  namespace Term
    @[reducible]
    def Halts (t₁: Term): Prop := ∃ t₂: Term, Eval t₁ t₂ ∧ IsValue t₂

    namespace IsValue
      theorem halts {t: Term}: IsValue t → Halts t
        | .bool _ => ⟨_, .refl, .bool _⟩
        | .nat  _ => ⟨_, .refl, .nat  _⟩
    end IsValue

    @[reducible]
    def Total (τ: Ty) (t: Term): Prop :=
      (HasType t τ) ∧ (Halts t) ∧ (
        match τ with
          | .bool => True
          | .nat  => True
      )

    namespace Total
      theorem halts {τ: Ty}: {t: Term} → Total τ t → Halts t
        | .bool _, _ => IsValue.halts (.bool _)
        | .nat _,  _ => IsValue.halts (.nat  _)

        | .unOp _ _,    ⟨_, ⟨_, he, hv⟩, _⟩
        | .binOp _ _ _, ⟨_, ⟨_, he, hv⟩, _⟩

        | .cond _ _ _,  ⟨_, ⟨_, he, hv⟩, _⟩ => ⟨_, he, hv⟩
    end Total

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

      theorem preservesTyping {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ
        | .unOp op _,       .unOp _ e => UnOp.Eval₁.preservesTyping op e
        | .unOp op operand, .unOpOp e => .unOp op (preservesTyping operand e)

        | .binOp op _ _,     .binOp    _ _ e => BinOp.Eval₁.preservesTyping op e
        | .binOp op lhs rhs, .binOpRight _ e => .binOp op lhs (preservesTyping rhs e)
        | .binOp op lhs rhs, .binOpLeft    e => .binOp op (preservesTyping lhs e) rhs

        | .cond _ t _, .condTrue  => t
        | .cond _ _ f, .condFalse => f
        | .cond c t f, .cond e    => .cond (preservesTyping c e) t f

      theorem preservesHalting {t₁ t₂: Term} (he: Eval₁ t₁ t₂): Halts t₁ ↔ Halts t₂ :=
        ⟨mp he, mpr he⟩
        where
          -- ∃ t₂: Term, Eval t₁ t₂ ∧ IsValue t₂
          mp {t₁ t₂: Term}: Eval₁ t₁ t₂ → Halts t₁ → Halts t₂
            | .unOp (.bool _) .not, _ => ⟨_, .refl, .bool _⟩

            | .unOpOp he₁, ⟨_, .trans he₂ he₃, hv⟩  => ⟨_, .trans _ he₂, hv⟩

            | .binOp (.bool _) (.bool _) .and,    _
            | .binOp (.bool _) (.bool _) .or,     _ => ⟨_, .refl, .bool _⟩
            | .binOp (.nat _)  (.nat _)  .add,    _
            | .binOp (.nat _)  (.nat _)  .mul,    _ => ⟨_, .refl, .nat _⟩
            | .binOp (.bool _) (.bool _) .eqBool, _
            | .binOp (.nat _)  (.nat _)  .eqNat,  _
            | .binOp (.nat _)  (.nat _)  .lt,     _
            | .binOp (.nat _)  (.nat _)  .lte,    _
            | .binOp (.nat _)  (.nat _)  .gt,     _
            | .binOp (.nat _)  (.nat _)  .gte,    _ => ⟨_, .refl, .bool _⟩

            | .binOpRight _ _, h      => ⟨_, sorry, sorry⟩
            | .binOpLeft _, h         => ⟨_, sorry, sorry⟩

            | .cond _, h              => ⟨_, sorry, sorry⟩
            | .condTrue, ⟨_, he, _⟩            => ⟨_, sorry, sorry⟩
            | .condFalse, h           => ⟨_, sorry, sorry⟩
          mpr {t₁ t₂: Term}: Eval₁ t₁ t₂ → Halts t₂ → Halts t₁
            | .unOp (.bool _) .not, _ => ⟨_, .refl, .bool _⟩
            | .unOpOp e, ⟨_, he, hv⟩  => ⟨_, .trans (.unOpOp e) he, hv⟩
            | .binOp _ _ _, h         => ⟨_, sorry, sorry⟩
            | .binOpRight _ _, h      => ⟨_, sorry, sorry⟩
            | .binOpLeft _, h         => ⟨_, sorry, sorry⟩
            | .cond _, h              => ⟨_, sorry, sorry⟩
            | .condTrue, h            => ⟨_, sorry, sorry⟩
            | .condFalse, h           => ⟨_, sorry, sorry⟩

      theorem preservesTotality {τ: Ty} {t₁ t₂: Term} (ht: HasType t₁ τ) (he: Eval₁ t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp {τ: Ty} {t₁ t₂: Term}: Eval₁ t₁ t₂ → Total τ t₁ → Total τ t₂ := sorry
          mpr {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval₁ t₁ t₂ → Total τ t₂ → Total τ t₁ := sorry
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

      theorem preservesTyping {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval t₁ t₂ → HasType t₂ τ
        | .bool, .refl          => .bool
        | .bool, .trans hxy hyz => sorry

        | .nat, .refl          => .nat
        | .nat, .trans hxy hyz => sorry

        | .unOp op operand, .refl => .unOp op (preservesTyping operand .refl)
        | .unOp op _, .trans (.unOp _ operand) hyz => sorry
        | .unOp op _, .trans (.unOpOp he)      hyz => sorry

        | .binOp op lhs rhs, .refl                       => .binOp op (preservesTyping lhs .refl) (preservesTyping rhs .refl)
        | .binOp op lhs rhs, .trans (.binOp o l r) .refl =>
          have ih := BinOp.Eval₁.preservesTyping op _
          have ih₁ := preservesTyping lhs .refl
          have ih₂ := preservesTyping rhs .refl
          .binOp ih ih₁ ih₂
        | .binOp op lhs rhs, .trans (.binOpRight hv he) hyz   =>
          have h := BinOp.Eval₁.preservesTyping op _
          have ih := preservesTyping (Eval₁.preservesTyping rhs he) (.trans he hyz)
          sorry
        | .binOp op lhs rhs, .trans (.binOpLeft he)     hyz   =>
          have h := BinOp.Eval₁.preservesTyping op _
          have ih := preservesTyping (Eval₁.preservesTyping lhs he) (.trans he hyz)
          sorry

        -- | .cond c t f, .refl                 => .cond (preservation c .refl) (preservation t .refl) (preservation f .refl)
        -- | .cond c t f, .trans .condTrue  hyz => sorry
        -- | .cond c t f, .trans (@Eval₁.condFalse .(t₁) .(t₂)) hyz => sorry
        -- | .cond c t f, .trans (.cond he) hyz => sorry

        | _, _ => sorry

      theorem preservesTotality {τ: Ty} {t₁ t₂: Term} (ht: HasType t₁ τ) (he: Eval t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp {τ: Ty} {t₁ t₂: Term}: Eval t₁ t₂ → Total τ t₁ → Total τ t₂ := sorry
          mpr {τ: Ty} {t₁ t₂: Term}: HasType t₁ τ → Eval t₁ t₂ → Total τ t₂ → Total τ t₁ := sorry

      theorem normalization {τ: Ty} {t: Term}: Halts t := sorry
    end Eval
  end Term

  namespace Top
    @[reducible]
    def Halts (t₁: Top): Prop := ∃ t₂: Top, Eval t₁ t₂ ∧ IsValue t₂

    namespace IsValue
      theorem halts {t: Top}: IsValue t → Halts t := nomatch t
    end IsValue

    @[reducible]
    def Total: Ty → Top → Prop
      | .bool, t => nomatch t

    namespace Total
      theorem halts {τ: Ty}: Top → Halts t
        | t => nomatch t
    end Total

    namespace HasType
      theorem deterministic {t: Top} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂
        | h, _ => nomatch h
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Top}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂
        | h, _ => nomatch h

      theorem progress {τ: Ty} {t₁: Top}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Top, Eval₁ t₁ t₂
        | h => nomatch h

      theorem preservesTyping {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ
        | h, _ => nomatch h

      theorem preservesHalting {t₁ t₂: Top} (he: Eval₁ t₁ t₂): Halts t₁ ↔ Halts t₂ :=
        ⟨mp he, mpr he⟩
        where
          mp {t₁ t₂: Top}: Eval₁ t₁ t₂ → Halts t₁ → Halts t₂
            | h, _ => nomatch h
          mpr {t₁ t₂: Top}: Eval₁ t₁ t₂ → Halts t₂ → Halts t₁
            | h, _ => nomatch h

      theorem preservesTotality {τ: Ty} {t₁ t₂: Top} (ht: HasType t₁ τ) (he: Eval₁ t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp {τ: Ty} {t₁ t₂: Top}: Eval₁ t₁ t₂ → Total τ t₁ → Total τ t₂ := sorry
          mpr {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval₁ t₁ t₂ → Total τ t₂ → Total τ t₁ := sorry
    end Eval₁

    namespace Eval
      theorem deterministic {t t₁ t₂: Top}: Eval t t₁ → Eval t t₂ → t₁ = t₂
        | h, _ => nomatch h

      theorem progress {τ: Ty} {t₁: Top}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Top, Eval t₁ t₂
        | h => nomatch h

      theorem preservesTyping {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval t₁ t₂ → HasType t₂ τ
        | h, _ => nomatch h

      theorem preservesTotality {τ: Ty} {t₁ t₂: Top} (ht: HasType t₁ τ) (he: Eval t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp {τ: Ty} {t₁ t₂: Top}: Eval t₁ t₂ → Total τ t₁ → Total τ t₂
            | h, _ => nomatch h

          mpr {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval t₁ t₂ → Total τ t₂ → Total τ t₁
            | h, _ => nomatch h

      theorem normalization {τ: Ty} {t: Top}: Halts t := nomatch t
    end Eval
  end Top
end Total.Stlc.Lang.Surface
