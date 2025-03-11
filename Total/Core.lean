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

  inductive Formals (ι: Type) (τ: Type): (α: Nat) → Domain τ α → Type where
    | nil (id: ι) (ty: τ): Formals ι τ 1 (.nil ty)
    | cons {α: Nat} {δ: Domain τ α} (id: ι) (ty: τ) (rest: Formals ι τ α δ): Formals ι τ α.succ (.cons ty δ)

  inductive Args (τ: Type) (μ: τ → Type): (α: Nat) → Domain τ α → Type where
    | nil {ty: τ} (arg: μ ty): Args τ μ 1 (.nil ty)
    | cons {α: Nat} {δ: Domain τ α} {τy: τ} (arg: μ ty) (rest: Args τ μ α δ): Args τ μ α.succ (.cons ty δ)
end Functions
