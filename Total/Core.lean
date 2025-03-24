section Identifiers
  structure Ident: Type where
    id: Option String
    idx: Nat

  namespace Ident
    def temp (idx: Nat): Ident := ⟨.none, idx⟩
  end Ident

  instance: BEq Ident where
    beq lhs rhs := lhs.idx == rhs.idx

  instance: ToString Ident where
    toString ident :=
      let pre := match ident.id with
        | .some id => id
        | .none    => ""
      pre ++ "$" ++ toString ident.idx
end Identifiers

section Functions
  inductive Domain (τ: Type): Nat → Type where
    | nil (ty: τ): Domain τ 1
    | cons {α: Nat} (ty: τ) (rest: Domain τ α): Domain τ α.succ

  inductive Params (ι: Type) (τ: Type): (α: Nat) → Domain τ α → Type where
    | nil (id: ι) (ty: τ): Params ι τ 1 (.nil ty)
    | cons {α: Nat} {δ: Domain τ α} (id: ι) (ty: τ) (rest: Params ι τ α δ): Params ι τ α.succ (.cons ty δ)

  inductive Args (τ: Type): (α: Nat) → Domain τ α → Type where
    | nil {ty: τ} (arg: τ): Args τ 1 (.nil ty)
    | cons {α: Nat} {δ: Domain τ α} {ty: τ} (arg: τ) (rest: Args τ α δ): Args τ α.succ (.cons ty δ)
end Functions
