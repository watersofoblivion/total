import Total.Core

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  mutual
    inductive Ty: Type where
      | bool: Ty
      | nat: Ty
      | fn {α: Nat} (δ: Domain α) (ρ: Ty): Ty

    inductive Domain: Nat → Type where
      | nil (τ: Ty): Domain 1
      | cons {α: Nat} (τ: Ty) (rest: Domain α): Domain α.succ
  end

  @[reducible]
  instance: {α β: Nat} → HAppend (Domain α) (Domain β) (Domain (β + α)) where
    hAppend lhs rhs :=
      append lhs rhs
      where
        @[reducible]
        append {α β: Nat}: Domain α → Domain β → Domain (β + α)
          | .nil τ,       δ => .cons τ δ
          | .cons τ rest, δ => .cons τ (append rest δ)

  @[reducible]
  instance: {α: Nat} → HAppend (Domain α) Ty (Domain (α + 1)) where
    hAppend lhs rhs :=
      append lhs rhs
      where
        @[reducible]
        append {α: Nat}: Domain α → Ty → Domain (α + 1)
          | .nil τ₁,       τ₂ => .cons τ₁ (.nil τ₂)
          | .cons τ₁ rest, τ₂ => .cons τ₁ (append rest τ₂)

  inductive PrimOp: {α: Nat} → Domain α → Ty → Type where
    | and: PrimOp (.cons .bool (.nil .bool)) .bool
    | or:  PrimOp (.cons .bool (.nil .bool)) .bool
    | not: PrimOp (.nil  .bool)              .bool

    | add: PrimOp (.cons .nat (.nil .nat)) .nat
    | mul: PrimOp (.cons .nat (.nil .nat)) .nat

    | eq  {τ: Ty}: PrimOp (.cons τ (.nil τ)) .bool
    | neq {τ: Ty}: PrimOp (.cons τ (.nil τ)) .bool

    | lt:  PrimOp (.cons .nat (.nil .nat)) .bool
    | lte: PrimOp (.cons .nat (.nil .nat)) .bool
    | gt:  PrimOp (.cons .nat (.nil .nat)) .bool
    | gte: PrimOp (.cons .nat (.nil .nat)) .bool

  mutual
    inductive Value: Ty → Type where
      | bool (b: Bool): Value .bool
      | nat (n: Nat): Value .nat

    inductive Values: {α: Nat} → Domain α → Type where
      | nil {τ: Ty} (v: Value τ): Values (.nil τ)
      | cons {τ: Ty} {α: Nat} {δ: Domain α} (v: Value τ) (rest: Values δ): Values (.cons τ δ)

    inductive Term: Ty → Type where
      | value {τ: Ty} (v: Value τ): Term τ
      | primOp {α: Nat} {δ: Domain α} {ρ: Ty} (op: PrimOp δ ρ) (operands: Args δ): Term ρ
      | cond {τ: Ty} (c: Term .bool) (t f: Term τ): Term τ

    inductive Terms: {α: Nat} → Domain α → Type where
      | nil {τ: Ty} (t: Term τ): Terms (.nil τ)
      | cons {τ: Ty} {α: Nat} {δ: Domain α} (t: Term τ) (rest: Terms δ): Terms (.cons τ δ)

    inductive Args: {α: Nat} → Domain α → Type where
      | terms {α: Nat} {δ: Domain α} (ts: Terms δ): Args δ
      | mix {α β: Nat} {δ₁: Domain α} {δ₂: Domain β} (vs: Values δ₁) (ts: Terms δ₂): Args (δ₁ ++ δ₂)
      | values {α: Nat} {δ: Domain α} (vs: Values δ): Args δ
  end

  @[reducible]
  instance: {α β: Nat} → {δ₁: Domain α} → {δ₂: Domain β} → HAppend (Values δ₁) (Values δ₂) (Values (δ₁ ++ δ₂)) where
    hAppend lhs rhs :=
      append lhs rhs
      where
        @[reducible]
        append {α β: Nat} {δ₁: Domain α} {δ₂: Domain β}: Values δ₁ → Values δ₂ → Values (δ₁ ++ δ₂)
          | .nil v,       vs => .cons v vs
          | .cons v rest, vs => .cons v (append rest vs)

  @[reducible]
  instance: {α: Nat} → {δ: Domain α} → {τ: Ty} → HAppend (Values δ) (Value τ) (Values (δ ++ τ)) where
    hAppend lhs rhs :=
      append lhs rhs
      where
        @[reducible]
        append {α: Nat} {δ: Domain α} {τ: Ty}: Values δ → Value τ → Values (δ ++ τ)
          | .nil v,       vs => .cons v (.nil vs)
          | .cons v rest, vs => .cons v (append rest vs)

  inductive Top: Ty → Type where
end Total.Stlc.Lang.Annotated
