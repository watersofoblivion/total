import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax

set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  /-!
  # Simply-Typed Lambda Calculus Surface Syntax Semantics

  These are the semantics of the language, given as inductive relations.
  -/

  namespace UnOp
/-!
# Unary Operators

Unary operators are primitive operations that operate on a single value
operand and produce a value result.  The type of the operand and the result
are not necessarily the same.

## Implemented Operators

There is one group of operators currently supported:

- **Logical**: Negation of boolean values (logical NOT)

The common operation of arithmetic negation is not supported as it is not
closed in the natural numbers.
-/

    /--
    ## Typing Relation

    The typing relation contains the allowed typing derevations for unary
    operators.

    ### Indexes

    The typing relation is indexed by three values:

    - The operator
    - The type of the operand
    - The type of the result
    -/
    inductive HasType: UnOp → Ty → Ty → Prop where
      /-- Logical Negation maps from Boolean values to Boolean values -/
      | not: HasType .not [Ty| 𝔹] [Ty| 𝔹]

    /--
    ## Single-Step Evaluation Relation

    The single-step evaluation relation contains all of the terms that can be
    computed in a single step by a unary operator.

    The inference rules in this relation take primitive Lean values instead of
    `Term`s since these are primitive operations that require their operand to
    be a value.  The rules for reducing the operand to a value are in the
    single-step evaluation relation for `Term`s.

    ### Indexes

    The single-step evaluation relation is indexed by three values:

    - The operator
    - The operand
    - The result
    -/
    inductive Eval₁: UnOp → Term → Term → Prop where
      /--
      Logical Negation takes a boolean `operand` and performs a logical `not` on
      it.
      -/
      | not {operand: Bool}: Eval₁ .not (.bool operand) (.bool !operand)
  end UnOp

  namespace BinOp
/-!
# Binary Operators

Unary operators are primitive operations that operate on two value
operands (a left-hand and a right-hand operand) and produce a value result.
The types of the left- and right-hand operands and the result are not
necessarily the same.

## Implemented Operators

There are four groups of operators currently supported:

- **Logical**: Conjuction and disjunction of boolean values (logical AND and
  logical OR)
- **Arithmetic**: Addition and multiplication of natural numbers.  These
  operations are supported because they are closed in the natural numbers,
  whereas the commonly included Subtraction, division, and modulus are not.
- **Equality**: Equals and Not Equals.  These operators are inherently
  polymorphic and are supported on both Boolean and Natural number values.
- **Comparison**: Less Than- and Greater Than- (or Equals) operators that
  compare natural numbers.
-/

    /--
    ## Typing Relation

    The typing relation contains the allowed typing derevations for binary
    operators.

    ### Indexes

    The typing relation is indexed by four values:

    - The operator
    - The type of the left-hand operand
    - The type of the right-hand operand
    - The type of the result
    -/
    inductive HasType: BinOp → Ty → Ty → Ty → Prop
      /--
      Logical Conjunction operates on Boolean inputs and produces a Boolean
      result.
      -/
      | and: HasType .and [Ty| 𝔹] [Ty| 𝔹] [Ty| 𝔹]
      /--
      Logical Disjunction operates on Boolean inputs and produces a Boolean
      result.
      -/
      | or:  HasType .or  [Ty| 𝔹] [Ty| 𝔹] [Ty| 𝔹]
      /--
      Addition operates on Nat inputs and produces a Nat result.
      -/
      | add: HasType .add [Ty| ℕ] [Ty| ℕ] [Ty| ℕ]
      /--
      Multiplication operates on Nat inputs and produces a Nat result.
      -/
      | mul: HasType .mul [Ty| ℕ] [Ty| ℕ] [Ty| ℕ]
      /--
      Equality operates on inputs with identical types and produces a Boolean
      result.
      -/
      | eq  {τ: Ty}: HasType .eq  [Ty| ‹τ›] [Ty| ‹τ›] [Ty| 𝔹]
      /--
      Inequality operates on inputs with identical types and produces a Boolean
      result.
      -/
      | neq {τ: Ty}: HasType .neq [Ty| ‹τ›] [Ty| ‹τ›] [Ty| 𝔹]
      /--
      Less Than operates on Nat inputs and produces a Boolean result.
      -/
      | lt:  HasType .lt  [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]
      /--
      Less Than or Equal operates on Nat inputs and produces a Boolean result.
      -/
      | lte: HasType .lte [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]
      /--
      Greater Than operates on Nat inputs and produces a Boolean result.
      -/
      | gt:  HasType .gt  [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]
      /--
      Greater Than or Equal operates on Nat inputs and produces a Boolean
      result.
      -/
      | gte: HasType .gte [Ty| ℕ] [Ty| ℕ] [Ty| 𝔹]

    /--
    ## Single-Step Evaluation Relation

    The single-step evaluation relation contains all of the terms that can be
    computed in a single step by a binary operator.

    The inference rules in this relation take primitive Lean values instead of
    `Term`s since these are primitive operations that require their operands to
    be values.  The rules for reducing the operands to values are in the
    single-step evaluation relation for `Term`s.

    ### Indexes

    The single-step evaluation relation is indexed by four values:

    - The operator
    - The left-hand operand
    - The right-hand operand
    - The result
    -/
    inductive Eval₁: BinOp → Term → Term → Term → Prop where
      /--
      Logical Conjuction takes two boolean values `lhs` and `rhs` and returns
      `lhs && rhs`.
      -/
      | and {lhs rhs: Bool}: Eval₁ .and [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs && rhs›]
      /--
      Logical Disjunction takes two boolean values `lhs` and `rhs` and returns
      `lhs || rhs`.
      -/
      | or  {lhs rhs: Bool}: Eval₁ .or  [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs || rhs›]
      /--
      Addition takes two natural number values `lhs` and `rhs` and returns their
      sum (`lhs + rhs`).
      -/
      | add {lhs rhs: Nat}:  Eval₁ .add [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹nat:lhs + rhs›]
      /--
      Multiplication takes two natural number values `lhs` and `rhs` and returns their
      product (`lhs * rhs`).
      -/
      | mul {lhs rhs: Nat}:  Eval₁ .mul [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹nat:lhs * rhs›]
      /--
      Boolean equality takes two boolean values `lhs` and `rhs` and returns
      `true` if they are equal and `false` otherwise (`lhs == rhs`).
      -/
      | eqBool  {lhs rhs: Bool}: Eval₁ .eq  [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs == rhs›]
      /--
      Natural number equality takes two natural number values `lhs` and `rhs` and
      returns `true` if they are equal and `false` otherwise (`lhs == rhs`).
      -/
      | eqNat   {lhs rhs: Nat}:  Eval₁ .eq  [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹bool:lhs == rhs›]
      /--
      Boolean inequality takes two boolean values `lhs` and `rhs` and returns
      `true` if they are unequal and `false` otherwise (`lhs != rhs`).
      -/
      | neqBool {lhs rhs: Bool}: Eval₁ .neq [Term| ‹bool:lhs›] [Term| ‹bool:rhs›] [Term| ‹bool:lhs != rhs›]
      /--
      Natural number inequality takes two natural number values `lhs` and `rhs`
      and returns `true` if they are unequal and `false` otherwise
      (`lhs != rhs`).
      -/
      | neqNat  {lhs rhs: Nat}:  Eval₁ .neq [Term| ‹nat:lhs›]  [Term| ‹nat:rhs›]  [Term| ‹bool:lhs != rhs›]
      /--
      Less than comparison takes two natural number values `lhs` and `rhs` and
      returns `true` if the first is less than the second (`lhs < rhs`).
      -/
      | lt  {lhs rhs: Nat}: Eval₁ .lt  [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs < rhs›]
      /--
      Less than or equal comparison takes two natural number values `lhs` and
      `rhs` and returns `true` if the first is less than or equal to the second
      (`lhs ≤ rhs`).
      -/
      | lte {lhs rhs: Nat}: Eval₁ .lte [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs ≤ rhs›]
      /--
      Greater than comparison takes two natural number values `lhs` and `rhs`
      and returns `true` if the first is greater than the second (`lhs > rhs`).
      -/
      | gt  {lhs rhs: Nat}: Eval₁ .gt  [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs > rhs›]
      /--
      Greater than or equal comparison takes two natural number values `lhs` and
      `rhs` and returns `true` if the first is greater than or equal to the
      second (`lhs ≥ rhs`).
      -/
      | gte {lhs rhs: Nat}: Eval₁ .gte [Term| ‹nat:lhs›] [Term| ‹nat:rhs›] [Term| ‹bool:lhs ≥ rhs›]
  end BinOp

  namespace Term
/-!
# Terms
-/

    /--
    ## Value Relation

    The value relation contains the terms that are values, i.e., terms that
    cannot be reduced any further by the evaluation rules.

    ### Indexes

    The value relation is indexed by one value:

    - The term
    -/
    inductive IsValue: Term → Prop where
      /-- Boolean literals are values -/
      | bool (b: Bool): IsValue [Term| ‹bool:b›]
      /-- Natural number literals are values -/
      | nat (n: Nat): IsValue [Term| ‹nat:n›]

    /--
    ## Typing Relation

    The typing relation contains the allowed typing derivations for terms.

    ### Indexes

    The value relation is indexed by two values:

    - The term
    - The term's derived type
    -/
    inductive HasType: Term → Ty → Prop where
      /-- Boolean literals are of Boolean type -/
      | bool {b: Bool}: HasType [Term| ‹bool:b›] [Ty| 𝔹]
      /-- Natural number literals are of Nat type -/
      | nat {n: Nat}: HasType [Term| ‹nat:n›] [Ty| ℕ]
      /--
      Unary operation expressions have the type of their result (`τ₂`).

      ### Premises

      - `h₁`: The unary operator maps from an input of type `τ₁` to a result of
        type `τ₂`
      - `h₂`: The operand has type `τ₁`.

      ### Conclusion

      The unary operator expression has type `τ₂`.
      -/
      | unOp {τ₁ τ₂: Ty} {op: UnOp} {operand: Term} (h₁: UnOp.HasType op τ₁ τ₂) (h₂: HasType operand τ₁): HasType (.unOp op operand) τ₂
      /--
      Binary operation expressions have the type of their result (`τ₃`).

      ### Premises

      - `h₁`: The binary operator maps from inputs of type `τ₁` and `τ₂` to a
        result of type `τ₃`
      - `h₂`: The left-hand side operand has type `τ₁`.
      - `h₃`: The left-hand side operand has type `τ₂`.

      ### Conclusion

      The binary operator expression has type `τ₃`.
      -/
      | binOp {τ₁ τ₂ τ₃: Ty} {op: BinOp} {lhs rhs: Term} (h₁: BinOp.HasType op τ₁ τ₂ τ₃) (h₂: HasType lhs τ₁) (h₃: HasType rhs τ₂): HasType (.binOp op lhs rhs) τ₃
      /--
      Conditional expressions have the type of their `then` and `else` clauses.
      The types of the clauses must be equal.

      ### Premises

      - `h₁`: The condition is of Boolean type
      - `h₂`: The `then` clause has some type `τ`.
      - `h₃`: The `else` clause has the same type `τ`.

      ### Conclusion

      The conditional operator expression has type `τ`.
      -/
      | cond {c t f: Term} {τ: Ty} (h₁: HasType c [Ty| 𝔹]) (h₂: HasType t τ) (h₃: HasType f τ): HasType [Term| if ‹c› then ‹t› else ‹f›] τ

    /--
    ## Single-Step Evaluation Relation

    The single-step evaluation relation contains all of the terms that can be
    computed in a single step.

    ### Indexes

    The value relation is indexed by two values:

    - The term being evaluated
    - The term it evaluates to
    -/
    inductive Eval₁: Term → Term → Prop where
      /--
      Unary operators applied to a value operand follow the unary operator
      single-step semantics.

      ### Premises

      - `h₁`: The operand is a value
      - `h₂`: A single-step unary operation evaluation

      ### Conclusion

      The term evaluates to the result of the unary operation evaluation.
      -/
      | unOp {op: UnOp} {operand res: Term} (h₁: IsValue operand) (h₂: UnOp.Eval₁ op operand res): Eval₁ (.unOp op operand) res
      /--
      Unary operators applied to a non-value operand evaluate the operand using
      the term single-step semantics.

      ### Premises

      - `h`: A single-step term evaluation of the operand

      ### Conclusion

      The operand takes an evaluation step.
      -/
      | unOpOp {op: UnOp} {operand₁ operand₂: Term} (h: Eval₁ operand₁ operand₂): Eval₁ (.unOp op operand₁) (.unOp op operand₂)
      /--
      Binary operators applied to two value operands follow the binary operator
      single-step semantics.

      ### Premises

      - `h₁`: The left-hand operand is a value
      - `h₂`: The right-hand operand is a value
      - `h₃`: A single-step binary operation evaluation

      ### Conclusion

      The term evaluates to the result of the binary operation evaluation.
      -/
      | binOp {op: BinOp} {lhs rhs res: Term} (h₁: IsValue lhs) (h₂: IsValue rhs) (h₃: BinOp.Eval₁ op lhs rhs res): Eval₁ (.binOp op lhs rhs) res
      /--
      Binary operators applied to a value left-hand operand and a non-value
      right-hand operand evaluate the right-hand operand using the term
      single-step semantics.

      ### Premises

      - `h₁`: The left-hand operand is a value
      - `h₂`: A single-step term evaluation of the right-hand operand

      ### Conclusion

      The right-hand operand takes an evaluation step.
      -/
      | binOpRight {op: BinOp} {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ (.binOp op lhs rhs₁) (.binOp op lhs rhs₂)
      /--
      Binary operators applied to non-value left- and right-hand operand
      evaluate the left-hand operand using the term single-step semantics.

      ### Premises

      - `h`: A single-step term evaluation of the left-hand operand

      ### Conclusion

      The left-hand operand takes an evaluation step.
      -/
      | binOpLeft {op: BinOp} {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ (.binOp op lhs₁ rhs) (.binOp op lhs₂ rhs)
      /--
      Conditional expressions with a condition of a literal `true` value
      evaluate to their `then` expression.

      ### Conclusion

      The conditional evalues to the `then` expression.
      -/
      | condTrue {t f: Term}: Eval₁ [Term| if tru then ‹t› else ‹f›] [Term| ‹t›]
      /--
      Conditional expressions with a condition of a literal `false` value
      evaluate to their `else` expression.

      ### Conclusion

      The conditional evalues to the `else` expression.
      -/
      | condFalse {t f: Term}: Eval₁ [Term| if fls then ‹t› else ‹f›] [Term| ‹f›]
      /--
      Conditional expressions with a non-value condition expression evaluate the
      condition expression using the term single-step semantics.

      ### Premises

      - `h`: A single-step term evaluation of the condition expression

      ### Conclusion

      The condition expression takes an evaluation step.
      -/
      | cond {c₁ c₂ t f: Term} (h: Eval₁ c₁ c₂): Eval₁ [Term| if ‹c₁› then ‹t› else ‹f›] [Term| if ‹c₂› then ‹t› else ‹f›]

    /--
    ## Multi-Step Evaluation Relation

    The multi-step evaluation relation for terms is the reflexive, transitive
    closure of the single-step evaluation relation for terms.
    -/
    abbrev Eval := RTC Eval₁
  end Term

  namespace Top
/-!
# Top-Level Terms
-/

    /--
    ## Value Relation

    TODO: Implement
    -/
    inductive IsValue: Top → Prop where

    /--
    ## Typing Relation

    TODO: Implement
    -/
    inductive HasType: Top → Ty → Prop where

    /--
    ## Single-Step Evaluation Relation

    TODO: Implement
    -/
    inductive Eval₁: Top → Top → Prop where

    /--
    ## Multi-Step Evalution Relation

    The multi-step evaluation relation for top-level terms is the reflexive,
    transitive closure of the single-step evaluation relation for top-level
    terms.
    -/
    abbrev Eval := RTC Eval₁
  end Top

  namespace File
/-!
# Files
-/
  end File
end Total.Stlc.Lang.Surface
