import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax

set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  section Types
  end Types

  namespace UnOp
    inductive HasType: UnOp → Ty → Ty → Prop where
      | not: HasType .not [Ty| 𝔹] [Ty| 𝔹]

    inductive Eval₁: UnOp → Term → Term → Prop where
      | not {operand: Bool}: Eval₁ .not (.bool operand) (.bool !operand)
  end UnOp

  namespace BinOp
    inductive HasType: BinOp → Ty → Ty → Ty → Prop
      | and: HasType .and [Ty| 𝔹] [Ty| 𝔹] [Ty| 𝔹]
      | or:  HasType .or  [Ty| 𝔹] [Ty| 𝔹] [Ty| 𝔹]
      | add: HasType .add [Ty| ℕ] [Ty| ℕ] [Ty| ℕ]
      | mul: HasType .mul [Ty| ℕ] [Ty| ℕ] [Ty| ℕ]
      | eq  {τ: Ty}: HasType .eq  [Ty| ‹τ›] [Ty| ‹τ›] [Ty| 𝔹]
      | neq {τ: Ty}: HasType .neq [Ty| ‹τ›] [Ty| ‹τ›] [Ty| 𝔹]
      | lt:  HasType .lt  [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]
      | lte: HasType .lte [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]
      | gt:  HasType .gt  [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]
      | gte: HasType .gte [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]

    inductive Eval₁: BinOp → Term → Term → Term → Prop where
      | and {lhs rhs: Bool}: Eval₁ .and [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs && rhs›]
      | or  {lhs rhs: Bool}: Eval₁ .or  [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs || rhs›]
      | add {lhs rhs: Nat}:  Eval₁ .add [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹nat:lhs + rhs›]
      | mul {lhs rhs: Nat}:  Eval₁ .mul [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹nat:lhs * rhs›]
      | eqBool  {lhs rhs: Bool}: Eval₁ .eq  [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs == rhs›]
      | eqNat   {lhs rhs: Nat}:  Eval₁ .eq  [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹bool:lhs == rhs›]
      | neqBool {lhs rhs: Bool}: Eval₁ .neq [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs != rhs›]
      | neqNat  {lhs rhs: Nat}:  Eval₁ .neq [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹bool:lhs != rhs›]
      | lt  {lhs rhs: Nat}: Eval₁ .lt  [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs < rhs›]
      | lte {lhs rhs: Nat}: Eval₁ .lte [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs ≤ rhs›]
      | gt  {lhs rhs: Nat}: Eval₁ .gt  [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs > rhs›]
      | gte {lhs rhs: Nat}: Eval₁ .gte [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs ≥ rhs›]
  end BinOp

  namespace Term
    inductive IsValue: Term → Prop where
      | bool (b: Bool): IsValue [Term| ‹bool:b›]
      | nat (n: Nat): IsValue [Term| ‹nat:n›]

    inductive HasType: Term → Ty → Prop where
      | bool {b: Bool}: HasType [Term| ‹bool:b›] [Ty| 𝔹]
      | nat {n: Nat}: HasType [Term| ‹nat:n›] [Ty| ℕ]
      | unOp {τ₁ τ₂: Ty} {op: UnOp} {operand: Term} (h₁: UnOp.HasType op τ₁ τ₂) (h₂: HasType operand τ₁): HasType (.unOp op operand) τ₂
      | binOp {τ₁ τ₂ τ₃: Ty} {op: BinOp} {lhs rhs: Term} (h₁: BinOp.HasType op τ₁ τ₂ τ₃) (h₂: HasType lhs τ₁) (h₃: HasType rhs τ₂): HasType (.binOp op lhs rhs) τ₃
      | cond {c t f: Term} {τ: Ty} (h₁: HasType c [Ty| 𝔹]) (h₂: HasType t τ) (h₃: HasType f τ): HasType [Term| if ‹c› then ‹t› else ‹f›] τ

    inductive Eval₁: Term → Term → Prop where
      | unOp {op: UnOp} {operand res: Term} (h₁: IsValue operand) (h₂: UnOp.Eval₁ op operand res): Eval₁ (.unOp op operand) res
      | unOpOp {op: UnOp} {operand₁ operand₂: Term} (h: Eval₁ operand₁ operand₂): Eval₁ (.unOp op operand₁) (.unOp op operand₂)

      | binOp {op: BinOp} {lhs rhs res: Term} (h₁: IsValue lhs) (h₂: IsValue rhs) (h₃: BinOp.Eval₁ op lhs rhs res): Eval₁ (.binOp op lhs rhs) res
      | binOpRight {op: BinOp} {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ (.binOp op lhs rhs₁) (.binOp op lhs rhs₂)
      | binOpLeft {op: BinOp} {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ (.binOp op lhs₁ rhs) (.binOp op lhs₂ rhs)

      | condTrue {t f: Term}: Eval₁ [Term| if tru then ‹t› else ‹f›] [Term| ‹t›]
      | condFalse {t f: Term}: Eval₁ [Term| if fls then ‹t› else ‹f›] [Term| ‹f›]
      | cond {c₁ c₂ t f: Term} (h: Eval₁ c₁ c₂): Eval₁ [Term| if ‹c₁› then ‹t› else ‹f›] [Term| if ‹c₂› then ‹t› else ‹f›]

    abbrev Eval := RTC Eval₁
  end Term

  namespace Top
    inductive IsValue: Top → Prop where
    inductive HasType: Top → Ty → Prop where
    inductive Eval₁: Top → Top → Prop where
    def Eval := RTC Eval₁
  end Top
end Total.Stlc.Lang.Surface
