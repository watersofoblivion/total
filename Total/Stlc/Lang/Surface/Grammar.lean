set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  inductive Ty: Type where
    | bool: Ty
    | nat: Ty

  inductive UnOp: Type where
    | not: UnOp

  inductive BinOp: Type where
    | and: BinOp
    | or:  BinOp
    | add: BinOp
    | mul: BinOp
    | eq:  BinOp
    | neq: BinOp
    | lt:  BinOp
    | lte: BinOp
    | gt:  BinOp
    | gte: BinOp

  inductive Term: Type where
    | bool (b: Bool): Term
    | nat  (n: Nat): Term
    | unOp (op: UnOp) (operand: Term): Term
    | binOp (op: BinOp) (lhs rhs: Term): Term
    | cond (c t f: Term): Term

  inductive Top: Type where
namespace Total.Stlc.Lang.Surface
