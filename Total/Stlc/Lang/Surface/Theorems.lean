import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax
import Total.Stlc.Lang.Surface.Semantics
import Total.Stlc.Lang.Surface.Termination

set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  /-!
  # Simply-Typed Lambda Calculus Surface Syntax Properties
  -/

  namespace Ty
/-!
# Types
-/
  end Ty

  namespace UnOp
/-!
# Unary Operators
-/

    variable {τ τ₁ τ₂: Ty}
    variable {op: UnOp}
    variable {t t₁ t₂: Term}

    namespace HasType
      theorem deterministic: HasType op τ τ₁ → HasType op τ τ₂ → τ₁ = τ₂
        | .not, .not => rfl
    end HasType

    namespace Eval₁
      theorem deterministic: Eval₁ op t t₁ → Eval₁ op t t₂ → t₁ = t₂
        | .not, .not => rfl

      theorem progress (_: Term.HasType t₁ τ₁): Term.IsValue t₁ → HasType op τ₁ τ₂ → ∃ t₂: Term, Eval₁ op t₁ t₂ ∧ Term.IsValue t₂
        | .bool _, .not => ⟨_, .not, .bool _⟩

      theorem preservesTyping: HasType op τ₁ τ₂ → Eval₁ op t₁ t₂ → Term.HasType t₂ τ₂
        | .not, .not => .bool

      theorem preservesHalting (he: Eval₁ op t₁ t₂): Halts op t₁ ↔ Term.Halts t₂ :=
        ⟨mp he, mpr he⟩
        where
          mp: Eval₁ op t₁ t₂ → Halts op t₁ → Term.Halts t₂
            | .not, ⟨_, .not, .bool _⟩ => ⟨_, .refl, .bool _⟩
          mpr: Eval₁ op t₁ t₂ → Term.Halts t₂ → Halts op t₁
            | .not, ⟨_, .refl, .bool _⟩ => ⟨_, .not, .bool _⟩

      theorem preservesTotality (ht: HasType op τ₁ τ₂) (he: Eval₁ op t₁ t₂): Total τ₁ τ₂ op t₁ ↔ Term.Total τ₂ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp: Eval₁ op t₁ t₂ → Total τ₁ τ₂ op t₁ → Term.Total τ₂ t₂
            | .not, ⟨.not, _⟩ => ⟨.bool, Term.IsValue.halts (.bool _), .intro⟩
          mpr: HasType op τ₁ τ₂ → Eval₁ op t₁ t₂ → Term.Total τ₂ t₂ → Total τ₁ τ₂ op t₁
            | .not, .not, ⟨.bool, _, _⟩ => ⟨.not, ⟨_, .not, .bool _⟩⟩
    end Eval₁
  end UnOp

  namespace BinOp
/-!
# Binary Operators
-/

    variable {τ τ₁ τ₂ τ₃ τ₄: Ty}
    variable {op: BinOp}
    variable {t t₁ t₂ t₃ t₄: Term}

    namespace HasType
      theorem deterministic: HasType op τ₁ τ₂ τ₃ → HasType op τ₁ τ₂ τ₄ → τ₃ = τ₄
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
      theorem deterministic: Eval₁ op t₁ t₂ t₃ → Eval₁ op t₁ t₂ t₄ → t₃ = t₄
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

      theorem progress (_: Term.HasType t₁ τ₁) (_: Term.HasType t₂ τ₂): Term.IsValue t₁ → Term.IsValue t₂ → HasType op τ₁ τ₂ τ₃ → ∃ t₃: Term, Eval₁ op t₁ t₂ t₃ ∧ Term.IsValue t₃
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

      theorem preservesTyping: HasType op τ₁ τ₂ τ₃ → Eval₁ op t₁ t₂ t₃ → Term.HasType t₃ τ₃
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

      theorem preservesHalting (he: Eval₁ op t₁ t₂ t₃): Halts op t₁ t₂ ↔ Term.Halts t₃ :=
        ⟨mp he, mpr he⟩
        where
          mp: Eval₁ op t₁ t₂ t₃ → Halts op t₁ t₂ → Term.Halts t₃
            | .and,     ⟨_, .and,     .bool _⟩
            | .or,      ⟨_, .or,      .bool _⟩ => ⟨_, .refl, .bool _⟩
            | .add,     ⟨_, .add,     .nat  _⟩
            | .mul,     ⟨_, .mul,     .nat  _⟩ => ⟨_, .refl, .nat  _⟩
            | .eqBool,  ⟨_, .eqBool,  .bool _⟩
            | .eqNat,   ⟨_, .eqNat,   .bool _⟩
            | .neqBool, ⟨_, .neqBool, .bool _⟩
            | .neqNat,  ⟨_, .neqNat,  .bool _⟩
            | .lt,      ⟨_, .lt,      .bool _⟩
            | .lte,     ⟨_, .lte,     .bool _⟩
            | .gt,      ⟨_, .gt,      .bool _⟩
            | .gte,     ⟨_, .gte,     .bool _⟩ => ⟨_, .refl, .bool _⟩
          mpr: Eval₁ op t₁ t₂ t₃ → Term.Halts t₃ → Halts op t₁ t₂
            | .and,     ⟨_, _, .bool _⟩ => ⟨_, .and,     .bool  _⟩
            | .or,      ⟨_, _, .bool _⟩ => ⟨_, .or,      .bool  _⟩
            | .add,     ⟨_, _, .nat  _⟩ => ⟨_, .add,     .nat   _⟩
            | .mul,     ⟨_, _, .nat  _⟩ => ⟨_, .mul,     .nat   _⟩
            | .eqBool,  ⟨_, _, .bool _⟩ => ⟨_, .eqBool,  .bool  _⟩
            | .eqNat,   ⟨_, _, .bool _⟩ => ⟨_, .eqNat,   .bool  _⟩
            | .neqBool, ⟨_, _, .bool _⟩ => ⟨_, .neqBool, .bool  _⟩
            | .neqNat,  ⟨_, _, .bool _⟩ => ⟨_, .neqNat,  .bool  _⟩
            | .lt,      ⟨_, _, .bool _⟩ => ⟨_, .lt,      .bool  _⟩
            | .lte,     ⟨_, _, .bool _⟩ => ⟨_, .lte,     .bool  _⟩
            | .gt,      ⟨_, _, .bool _⟩ => ⟨_, .gt,      .bool  _⟩
            | .gte,     ⟨_, _, .bool _⟩ => ⟨_, .gte,     .bool  _⟩

      theorem preservesTotality (ht: HasType op τ₁ τ₂ τ₃) (he: Eval₁ op t₁ t₂ t₃): Total τ₁ τ₂ τ₃ op t₁ t₂ ↔ Term.Total τ₃ t₃ :=
        ⟨mp he, mpr ht he⟩
        where
          mp: Eval₁ op t₁ t₂ t₃ → Total τ₁ τ₂ τ₃ op t₁ t₂ → Term.Total τ₃ t₃
            | .and,     ⟨.and, _⟩
            | .or,      ⟨.or,  _⟩ => ⟨.bool, Term.IsValue.halts (.bool _), .intro⟩
            | .add,     ⟨.add, _⟩
            | .mul,     ⟨.mul, _⟩ => ⟨.nat,  Term.IsValue.halts (.nat  _), .intro⟩
            | .eqBool,  ⟨.eq,  _⟩
            | .eqNat,   ⟨.eq,  _⟩
            | .neqBool, ⟨.neq, _⟩
            | .neqNat,  ⟨.neq, _⟩
            | .lt,      ⟨.lt,  _⟩
            | .lte,     ⟨.lte, _⟩
            | .gt,      ⟨.gt,  _⟩
            | .gte,     ⟨.gte, _⟩ => ⟨.bool, Term.IsValue.halts (.bool _), .intro⟩
          mpr: HasType op τ₁ τ₂ τ₃ → Eval₁ op t₁ t₂ t₃ → Term.Total τ₃ t₃ → Total τ₁ τ₂ τ₃ op t₁ t₂
            | .and, .and,     ⟨.bool, _, _⟩ => ⟨.and, ⟨_, .and,     .bool _⟩⟩
            | .or,  .or,      ⟨.bool, _, _⟩ => ⟨.or,  ⟨_, .or,      .bool _⟩⟩
            | .add, .add,     ⟨.nat,  _, _⟩ => ⟨.add, ⟨_, .add,     .nat  _⟩⟩
            | .mul, .mul,     ⟨.nat,  _, _⟩ => ⟨.mul, ⟨_, .mul,     .nat  _⟩⟩
            | .eq, .eqBool,   ⟨.bool, _, _⟩ => ⟨.eq,  ⟨_, .eqBool,  .bool _⟩⟩
            | .eq, .eqNat,    ⟨.bool, _, _⟩ => ⟨.eq,  ⟨_, .eqNat,   .bool _⟩⟩
            | .neq, .neqBool, ⟨.bool, _, _⟩ => ⟨.neq, ⟨_, .neqBool, .bool _⟩⟩
            | .neq, .neqNat,  ⟨.bool, _, _⟩ => ⟨.neq, ⟨_, .neqNat,  .bool _⟩⟩
            | .lt,  .lt,      ⟨.bool, _, _⟩ => ⟨.lt,  ⟨_, .lt,      .bool _⟩⟩
            | .lte, .lte,     ⟨.bool, _, _⟩ => ⟨.lte, ⟨_, .lte,     .bool _⟩⟩
            | .gt,  .gt,      ⟨.bool, _, _⟩ => ⟨.gt,  ⟨_, .gt,      .bool _⟩⟩
            | .gte, .gte,     ⟨.bool, _, _⟩ => ⟨.gte, ⟨_, .gte,     .bool _⟩⟩
    end Eval₁
  end BinOp

  namespace Term
/-!
# Terms
-/

    variable {τ τ₁ τ₂: Ty}
    variable {t t₁ t₂: Term}

    namespace HasType
      theorem deterministic {t: Term} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂
        | .bool,          .bool
        | .nat,           .nat           => rfl
        | .unOp  op₁ operand₁,   .unOp  op₂ operand₂   =>
          have ih₁ := deterministic operand₁ operand₂
          have op₁ := by rw [ih₁] at op₁; exact op₁
          UnOp.HasType.deterministic op₁ op₂
        | .binOp op₁ lhs₁ rhs₁, .binOp op₂ lhs₂ rhs₂ =>
          have ih₁ := deterministic lhs₁ lhs₂
          have ih₂ := deterministic rhs₁ rhs₂
          have op₁ := by rw [ih₁, ih₂] at op₁; exact op₁
          BinOp.HasType.deterministic op₁ op₂
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
          match progress operand with
            | .inl v =>
              have ⟨_, e, _⟩ := UnOp.Eval₁.progress operand v op
              .inr ⟨_, .unOp v e⟩
            | .inr ⟨_, e⟩ => .inr ⟨_, .unOpOp e⟩

        | .binOp op lhs rhs =>
          match progress lhs, progress rhs with
            | .inl v₁, .inl v₂ =>
              have ⟨_, e, _⟩ := BinOp.Eval₁.progress lhs rhs v₁ v₂ op
              .inr ⟨_, .binOp v₁ v₂ e⟩
            | .inl v,       .inr ⟨_, e⟩ => .inr ⟨_, .binOpRight v e⟩
            | .inr ⟨_, e⟩,  _           => .inr ⟨_, .binOpLeft e⟩

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

      theorem preservesHalting (he: Eval₁ t₁ t₂): Halts t₁ ↔ Halts t₂ :=
        ⟨mp he, mpr he⟩
        where
          mp: Eval₁ t₁ t₂ → Halts t₁ → Halts t₂
            | h, ⟨_, .trans he₁ he₂, hv⟩ =>
              have hd := deterministic h he₁
              have he := by rw [←hd] at he₂; exact he₂
              ⟨_, he, hv⟩
          mpr: Eval₁ t₁ t₂ → Halts t₂ → Halts t₁
            | h, ⟨_, .refl, hv⟩          => ⟨_, .trans h .refl, hv⟩
            | h, ⟨_, .trans he₁ he₂, hv⟩ => ⟨_, .trans h (.trans he₁ he₂), hv⟩

      theorem preservesTotality (ht: HasType t₁ τ) (he: Eval₁ t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp: Eval₁ t₁ t₂ → Total τ t₁ → Total τ t₂
            | he₁, ⟨ht, ⟨_, .trans he₂ he₃, hv⟩, t⟩ =>
              have hd := deterministic he₁ he₂
              have ht := preservesTyping ht he₁
              have he := by rw [←hd] at he₃; exact he₃
              ⟨ht, ⟨_, he, hv⟩, t⟩
          mpr: HasType t₁ τ → Eval₁ t₁ t₂ → Total τ t₂ → Total τ t₁
            | ht, he₁, ⟨_, ⟨_, .refl,          v⟩, t⟩ => ⟨ht, ⟨_, .trans he₁ .refl,            v⟩, t⟩
            | ht, he₁, ⟨_, ⟨_, .trans he₂ he₃, v⟩, t⟩ => ⟨ht, ⟨_, .trans he₁ (.trans he₂ he₃), v⟩, t⟩
    end Eval₁

    namespace Eval
      theorem deterministic {t t₁ t₂: Term}: Eval t t₁ → Eval t t₂ → t₁ = t₂
        | .refl,            .refl            => rfl
        | .refl,            .trans _ _       => sorry
        | .trans _ _,       .refl            => sorry
        | .trans hxy₁ hyz₁, .trans hxy₂ hyz₂ =>
          have ih := Eval₁.deterministic hxy₁ hxy₂
          have h := by rw [ih] at hyz₁; exact hyz₁
          deterministic h hyz₂

      theorem progress {τ: Ty} {t₁: Term} (ht₁: HasType t₁ τ): ∃ t₂: Term, Eval t₁ t₂ ∧ IsValue t₂ :=
        match Eval₁.progress ht₁ with
          | .inl v       => ⟨_, .refl, v⟩
          | .inr ⟨_, e₁⟩ =>
            have ht₂ := Eval₁.preservesTyping ht₁ e₁
            have ⟨_, e₂, v⟩ := progress ht₂
            ⟨_, .trans e₁ e₂, v⟩

      theorem preservesTyping {τ: Ty} {t₁ t₂: Term} (h: HasType t₁ τ): Eval t₁ t₂ → HasType t₂ τ
        | .refl          => h
        | .trans hxy hyz =>
          have ih := Eval₁.preservesTyping h hxy
          preservesTyping ih hyz

      theorem preservesTotality {τ: Ty} {t₁ t₂: Term} (ht: HasType t₁ τ) (he: Eval t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp {τ: Ty} {t₁ t₂: Term}: Eval t₁ t₂ → Total τ t₁ → Total τ t₂
            | .refl,          h           => h
            | .trans hxy hyz, ⟨ht, hh, t⟩ =>
              have ih := Eval₁.preservesTotality ht hxy
                |>.mp ⟨ht, hh, t⟩
              mp hyz ih
          mpr {τ: Ty} {t₁ t₂: Term} (h₁: HasType t₁ τ): Eval t₁ t₂ → Total τ t₂ → Total τ t₁
            | .refl,          t => t
            | .trans hxy hyz, t =>
              have ih₁ := Eval₁.preservesTyping h₁ hxy
              have ih₂ := mpr ih₁ hyz t
              Eval₁.preservesTotality h₁ hxy
                |>.mpr ih₂

      theorem normalization {τ: Ty} {t: Term}: HasType t τ → Halts t
        | .bool => Term.IsValue.halts (.bool _)
        | .nat  => Term.IsValue.halts (.nat  _)
        | .unOp op operand  => sorry
        | .binOp op lhs rhs => sorry
        | .cond c t f       => sorry
    end Eval
  end Term

  namespace Top
/-!
# Top-Level Terms
-/

    variable {τ τ₁ τ₂: Ty}
    variable {t t₁ t₂: Top}

    namespace HasType
      theorem deterministic {t: Top} {τ₁ τ₂: Ty}: HasType t τ₁ → HasType t τ₂ → τ₁ = τ₂ := nomatch t
    end HasType

    namespace Eval₁
      theorem deterministic {t t₁ t₂: Top}: Eval₁ t t₁ → Eval₁ t t₂ → t₁ = t₂ := nomatch t
      theorem progress {τ: Ty} {t₁: Top}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Top, Eval₁ t₁ t₂ := nomatch t₁
      theorem preservesTyping {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval₁ t₁ t₂ → HasType t₂ τ := nomatch t₁
      theorem preservesHalting {t₁ t₂: Top} (he: Eval₁ t₁ t₂): Halts t₁ ↔ Halts t₂ :=
        ⟨mp he, mpr he⟩
        where
          mp {t₁ t₂: Top}: Eval₁ t₁ t₂ → Halts t₁ → Halts t₂ := nomatch t₁
          mpr {t₁ t₂: Top}: Eval₁ t₁ t₂ → Halts t₂ → Halts t₁ := nomatch t₁
      theorem preservesTotality {τ: Ty} {t₁ t₂: Top} (ht: HasType t₁ τ) (he: Eval₁ t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp {τ: Ty} {t₁ t₂: Top}: Eval₁ t₁ t₂ → Total τ t₁ → Total τ t₂ := nomatch t₁
          mpr {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval₁ t₁ t₂ → Total τ t₂ → Total τ t₁ := nomatch t₁
    end Eval₁

    namespace Eval
      theorem deterministic {t t₁ t₂: Top}: Eval t t₁ → Eval t t₂ → t₁ = t₂ := nomatch t
      theorem progress {τ: Ty} {t₁: Top}: HasType t₁ τ → IsValue t₁ ∨ ∃ t₂: Top, Eval t₁ t₂ := nomatch t₁
      theorem preservesTyping {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval t₁ t₂ → HasType t₂ τ := nomatch t₁
      theorem preservesTotality {τ: Ty} {t₁ t₂: Top} (ht: HasType t₁ τ) (he: Eval t₁ t₂): Total τ t₁ ↔ Total τ t₂ :=
        ⟨mp he, mpr ht he⟩
        where
          mp {τ: Ty} {t₁ t₂: Top}: Eval t₁ t₂ → Total τ t₁ → Total τ t₂ := nomatch t₁
          mpr {τ: Ty} {t₁ t₂: Top}: HasType t₁ τ → Eval t₁ t₂ → Total τ t₂ → Total τ t₁ := nomatch t₁
      theorem normalization {τ: Ty} {t: Top}: Halts t := nomatch t
    end Eval
  end Top

  namespace File
/-!
# Files
-/

  end File
end Total.Stlc.Lang.Surface
