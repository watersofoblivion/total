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

  inductive Params {τ: Type}: {α: Nat} → Domain τ α → Type where
    | nil (id: Nat) (ty: τ): Params (.nil ty)
    | cons {α: Nat} {δ: Domain τ α} (id: ι) (ty: τ) (rest: Params δ): Params (.cons ty δ)

  inductive Args {τ: Type} (t: τ → Type): {α: Nat} → Domain τ α → Type where
    | nil {ty: τ} (arg: t ty): Args t (.nil ty)
    | cons {α: Nat} {δ: Domain τ α} {ty: τ} (arg: t ty) (rest: Args t δ): Args t (.cons ty δ)

  inductive Values {τ: Type} (t: τ → Type) (υ: {ty: τ} → t ty → Prop): {α: Nat} -> Domain τ α → Type where
    | nil {ty: τ} {term: t ty} (v: υ term): Values t υ (.nil ty)
    | cons {α: Nat} {δ: Domain τ α} {ty: τ} {term: t ty} (v: υ term) /- (rest: Values t υ δ) -/: Values t υ (.cons ty δ)
end Functions
