namespace Total.Stlc.Lang.Surface
  mutual
    inductive Ty: Type where
      | bool: Ty
      | nat: Ty
      -- | fn (dom: List Ty) (rng: Ty): Ty
  end

  inductive Term: Type where
    | bool (b: Bool): Term
    | nat  (n: Nat): Term
    | and (lhs rhs: Term): Term
    | or (lhs rhs: Term): Term
    | not (op: Term): Term
    | add (lhs rhs: Term): Term
    | sub (lhs rhs: Term): Term
    | mul (lhs rhs: Term): Term
    | eq (lhs rhs: Term): Term
    | neq (lhs rhs: Term): Term
    | lt (lhs rhs: Term): Term
    | lte (lhs rhs: Term): Term
    | gt (lhs rhs: Term): Term
    | gte (lhs rhs: Term): Term
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
