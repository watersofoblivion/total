import Total.Core

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  mutual
    inductive Ty: Type where
      | bool: Ty
      | nat: Ty
      | fn {α: Nat} (dom: Domain α) (rng: Ty): Ty

    inductive Domain: Nat → Type where
      | nil (τ: Ty): Domain 1
      | cons {α: Nat} (τ: Ty) (rest: Domain α): Domain α.succ
  end

  instance: {α β: Nat} → HAppend (Domain α) (Domain β) (Domain (β + α)) where
    hAppend lhs rhs :=
      append lhs rhs
      where
        append {α β: Nat}: Domain α → Domain β → Domain (β + α)
          | .nil τ, δ => .cons τ δ
          | .cons τ rest, δ => .cons τ (append rest δ)

  inductive PrimOp: {α: Nat} → Domain α → Ty → Type where
    | and: PrimOp (.cons .bool (.nil .bool)) .bool
    | or:  PrimOp (.cons .bool (.nil .bool)) .bool
    | not: PrimOp (.nil .nat)        .bool

    | add: PrimOp (.cons .nat (.nil .nat)) .nat
    | sub: PrimOp (.cons .nat (.nil .nat)) .nat
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
      | primOp {α: Nat} {δ: Domain α} {τ: Ty}  (op: PrimOp δ τ) (operands: Args δ): Term (.fn δ τ)
      | cond {τ: Ty} (c: Term .bool) (t f: Term τ): Term τ

    inductive Terms: {α: Nat} → Domain α → Type where
      | nil {τ: Ty} (t: Term τ): Terms (.nil τ)
      | cons {τ: Ty} {α: Nat} {δ: Domain α} (t: Term τ) (rest: Terms δ): Terms (.cons τ δ)

    inductive Args: {α: Nat} → Domain α → Type where
      | terms {α: Nat} {δ: Domain α} (ts: Terms δ): Args δ
      | mix {α β: Nat} {δ₁: Domain α} {δ₂: Domain β} (vs: Values δ₁) (ts: Terms δ₂): Args (δ₁ ++ δ₂)
      | values {α: Nat} {δ: Domain α} (vs: Values δ): Args δ
  end

  inductive Top: Ty → Type where
end Total.Stlc.Lang.Annotated
