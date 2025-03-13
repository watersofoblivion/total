namespace Total.Stlc.Lang.Surface
  inductive Ty: Type where
    | bool: Ty
    | nat: Ty
    -- | fn (dom: List Ty) (rng: Ty): Ty

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
    -- | var  (id: String): Term
    -- | bind (id: String) (ty: Ty) (expr: Term) (scope: Term): Term
    -- | abs (params: List (String × Ty)) (body: Term): Term
    -- | app (fn: Term) (args: List Term): Term

  inductive Top: Type where
    -- | val (id: String) (ty: Ty) (value: Term): Top
    -- | defn (id: String) (args: List (String × Ty)) (body: Term): Top
    -- | letVal (id: String) (ty: Ty) (value: Term): Top
    -- | letDefn (id: String) (args: List (String × Ty)) (body: Term): Top
namespace Total.Stlc.Lang.Surface
