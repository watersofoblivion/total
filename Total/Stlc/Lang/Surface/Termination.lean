import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax
import Total.Stlc.Lang.Surface.Semantics

set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  /-!
  # Simply-Typed Lambda Calculus Surface Syntax Termination Semantics

  These are the termination-specific semantics of the language.

  These are separate from the main semantics of the language as they are defined
  in terms of those main semantics.
  -/

  namespace UnOp
/-!
# Unary Operators
-/

    variable {τ₁ τ₂: Ty}
    variable {op: UnOp}
    variable {operand: Term}

    /--
    ## Halts

    A unary operator `op` halts when applied to an operand `operand₁` if the
    application evaluates to a value `operand₂`.
    -/
    @[reducible]
    def Halts (op: UnOp) (operand₁: Term): Prop := ∃ operand₂: Term, Eval₁ op operand₁ operand₂ ∧ Term.IsValue operand₂

    /--
    ## Totality

    A unary operator `op` that takes operands of type `τ₁` and produces results
    of type `τ₂` is total when applied to `operand` if the application halts.
    -/
    @[reducible]
    def Total (τ₁ τ₂: Ty) (op: UnOp) (operand: Term): Prop :=
      (HasType op τ₁ τ₂) ∧ (Halts op operand)

    namespace Total
/-!
## Termination of Total Unary Operations
-/

      /--
      Total unary operator applications halt.
      -/
      theorem halts: Total τ₁ τ₂ op operand → Halts op operand
        | ⟨_, hh⟩ => hh
    end Total
  end UnOp

  namespace BinOp
/-!
# Binary Operators
-/
    variable {τ₁ τ₂ τ₃: Ty}
    variable {op: BinOp}
    variable {lhs rhs: Term}

    /--
    ## Halts

    A binary operator `op` halts when applied to left- and right-hand operands
    `lhs` and `rhs` if the application evaluates to a value `res`.
    -/
    @[reducible]
    def Halts (op: BinOp) (lhs rhs: Term): Prop := ∃ res: Term, Eval₁ op lhs rhs res ∧ Term.IsValue res

    /--
    ## Totality

    A binary operator `op` that takes operands of type `τ₁` and `τ₂` and
    produces results of type `τ₃` is total when applied to left- and right-hand
    operands `lhs` and `rhs` if the application halts.
    -/
    @[reducible]
    def Total (τ₁ τ₂ τ₃: Ty) (op: BinOp) (lhs rhs: Term): Prop :=
      (HasType op τ₁ τ₂ τ₃) ∧ (Halts op lhs rhs)

    namespace Total
/-!
## Termination of Total Binary Operations
-/

      /--
      Total binary operator applications halt.
      -/
      theorem halts: Total τ₁ τ₂ τ₃ op lhs rhs → Halts op lhs rhs
        | ⟨_, hh⟩ => hh
    end Total
  end BinOp

  namespace Term
/-!
# Terms
-/
    variable {τ: Ty}
    variable {t: Term}

    /--
    ## Halts

    A term `t₁` halts if it evaluates to a value `t₂`.
    -/
    @[reducible]
    def Halts (t₁: Term): Prop := ∃ t₂: Term, Eval t₁ t₂ ∧ IsValue t₂

    /--
    ## Totality

    A term `t` of type `τ` is total if it halts and one of the following:

    - It is of type boolean
    - It is of type nat
    -/
    @[reducible]
    def Total (τ: Ty) (t: Term): Prop :=
      (HasType t τ) ∧ (Halts t) ∧ (
        match τ with
          | .bool => True
          | .nat  => True
      )

    namespace IsValue
/-!
## Termination of Values
-/

      /--
      Values halt.
      -/
      theorem halts: IsValue t → Halts t
        | .bool _ => ⟨_, .refl, .bool _⟩
        | .nat  _ => ⟨_, .refl, .nat  _⟩
    end IsValue

    namespace Total
/-!
## Termination of Total Terms
-/

      /--
      Total terms halt.
      -/
      theorem halts: {t: Term} → Total τ t → Halts t
        | .bool  _,     _                   => IsValue.halts (.bool _)
        | .nat   _,     _                   => IsValue.halts (.nat  _)

        | .unOp  _ _,   ⟨_, ⟨_, he, hv⟩, _⟩
        | .binOp _ _ _, ⟨_, ⟨_, he, hv⟩, _⟩

        | .cond  _ _ _, ⟨_, ⟨_, he, hv⟩, _⟩ => ⟨_, he, hv⟩
    end Total
  end Term

  namespace Top
/-!
# Top-Level Terms
-/

    variable {τ: Ty}
    variable {t: Top}

    /--
    ## Halts

    A top-level term `t₁` halts if it evaluates to a value `t₂`.
    -/
    @[reducible]
    def Halts (t₁: Top): Prop := ∃ t₂: Top, Eval t₁ t₂ ∧ IsValue t₂

    /--
    ## Totality

    A top-level term `t` of type `τ` is total if it halts and one of the
    following:

    - It is of type boolean
    - It is of type nat
    -/
    @[reducible]
    def Total: Ty → Top → Prop
      | .bool, t => nomatch t

    namespace IsValue
/-!
## Termination of Values
-/

      /--
      Values halt.
      -/
      theorem halts: IsValue t → Halts t := nomatch t
    end IsValue

    namespace Total
/-!
## Termination of Total Terms
-/

      /--
      Total terms halt.
      -/
      theorem halts {t: Top}: Total τ t → Halts t := nomatch t
    end Total
  end Top

  namespace File
/-!
# Files
-/

  end File
end Total.Stlc.Lang.Surface
