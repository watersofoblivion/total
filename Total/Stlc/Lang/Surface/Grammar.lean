set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  /-!
  # Simply-Typed Lambda Calculus Surface Syntax Grammar

  These are the inductive types defined for representing terms of the surface
  syntax.
  -/

  /--
  # Types

  Representation of types.
  -/
  inductive Ty: Type where
     /-- Booleans -/
    | bool: Ty
    /-- Natural Numbers -/
    | nat: Ty

  /--
  # Unary Operators

  The supported unary operators.

  These are bare operators and unary operator expressions.  The representation
  of the latter is in the type for `Term`s.
  -/
  inductive UnOp: Type where
    /-- Logical Negation -/
    | not: UnOp

  /--
  # Binary Operators

  The supported binary operators.

  These are bare operators and binary operator expressions.  The representation
  of the latter is in the type for `Term`s.
  -/
  inductive BinOp: Type where
    /-- Logical Conjunction (AND) -/
    | and: BinOp
    /-- Logical Disjunction (OR) -/
    | or:  BinOp
    /-- Addition -/
    | add: BinOp
    /-- Multiplication -/
    | mul: BinOp
    /-- Boolean Equality -/
    | eq:  BinOp
    /-- Boolean Inequality -/
    | neq: BinOp
    /-- Less Than -/
    | lt:  BinOp
    /-- Less Than or Equal -/
    | lte: BinOp
    /-- Greater Than -/
    | gt:  BinOp
    /-- Greater Than or Equal -/
    | gte: BinOp

  /--
  # Terms

  Terms of the language.
  -/
  inductive Term: Type where
    /-- Boolean literal -/
    | bool (b: Bool): Term
    /-- Natural number literal -/
    | nat  (n: Nat): Term
    /-- Unary operator application -/
    | unOp (op: UnOp) (operand: Term): Term
    /-- Binary operator application -/
    | binOp (op: BinOp) (lhs rhs: Term): Term
    /-- Conditional expression -/
    | cond (c t f: Term): Term

  /--
  # Top-Level Terms

  Top-level terms of the language.
  -/
  inductive Top: Type where

  /--
  # Files

  Source files.
  -/
  structure File: Type where
    /--
    The top-level terms in the file, in the order present in the file.
    -/
    tops: List Top
namespace Total.Stlc.Lang.Surface
