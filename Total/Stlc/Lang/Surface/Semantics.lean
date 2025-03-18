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

    -- def Eval := RTC Eval₁
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

    -- def Eval := RTC Eval₁
  end BinOp

  namespace Term
    inductive IsValue: Term → Prop where
      | bool (b: Bool): IsValue [Term| ‹bool:b›]
      | nat (n: Nat): IsValue [Term| ‹nat:n›]
      -- | var (id: String): IsValue (.var id)
      -- | abs (params: List (String × Ty)) (body: Term): IsValue (.abs params body)

    inductive HasType: Term → Ty → Prop where
      | bool {b: Bool}: HasType [Term| ‹bool:b›] [Ty| 𝔹]
      | nat {n: Nat}: HasType [Term| ‹nat:n›] [Ty| ℕ]
      | unOp {τ₁ τ₂: Ty} {op: UnOp} {operand: Term} (h₁: UnOp.HasType op τ₁ τ₂) (h₂: HasType operand τ₁): HasType (.unOp op operand) τ₂
      | binOp {τ₁ τ₂ τ₃: Ty} {op: BinOp} {lhs rhs: Term} (h₁: BinOp.HasType op τ₁ τ₂ τ₃) (h₂: HasType lhs τ₁) (h₃: HasType rhs τ₂): HasType (.binOp op lhs rhs) τ₃
      | cond {c t f: Term} {τ: Ty} (h₁: HasType c [Ty| 𝔹]) (h₂: HasType t τ) (h₃: HasType f τ): HasType [Term| if ‹c› then ‹t› else ‹f›] τ
      -- | var  {τ: Ty}: HasType _ τ
      -- | bind {expr scope: Term} {τ₁ τ₂: Ty} (h₁: HasType expr τ₁) (h₂: HasType (ε.bind ι τ₁) scope τ₂): HasType (.bind t₁ expr scope) τ₂
      -- TODO: Turn List.{foldl,map} applications into functions on FormalList
      -- | abs {formals: FormalList} {body: Term} {τ: Ty} (h: HasType (List.foldl (fun ε (ι, τ) => ε.bind ι τ) ε formals) body τ): HasType (.abs formals body) (.fn (List.map (·.snd) formals) τ)
      -- TODO: Turn List.{foldl,zip} applications into functions on FormalList
      -- ERROR: Free Variable Somewhere?!?!
      -- | app {params: ParamList} {res: Ty} {fn: Term} {args: ArgList} (h₁: HasType fn (.fn params res)) (h₂: List.foldl (fun p (t, τ) => p ∧ HasType t τ) true (List.zip args params)): HasType (.app fn args) res

    inductive Eval₁: Term → Term → Prop where
      | unOp {op: UnOp} {operand res: Term} (h₁: IsValue operand) (h₂: UnOp.Eval₁ op operand res): Eval₁ (.unOp op operand) res
      | unOpOp {op: UnOp} {operand₁ operand₂: Term} (h: Eval₁ operand₁ operand₂): Eval₁ (.unOp op operand₁) (.unOp op operand₂)

      | binOp {op: BinOp} {lhs rhs res: Term} (h₁: IsValue lhs) (h₂: IsValue rhs) (h₃: BinOp.Eval₁ op lhs rhs res): Eval₁ (.binOp op lhs rhs) res
      | binOpRight {op: BinOp} {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ (.binOp op lhs rhs₁) (.binOp op lhs rhs₂)
      | binOpLeft {op: BinOp} {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ (.binOp op lhs₁ rhs) (.binOp op lhs₂ rhs)

      | condTrue {t f: Term}: Eval₁ [Term| if tru then ‹t› else ‹f›] [Term| ‹t›]
      | condFalse {t f: Term}: Eval₁ [Term| if fls then ‹t› else ‹f›] [Term| ‹f›]
      | cond {c₁ c₂ t f: Term} (h: Eval₁ c₁ c₂): Eval₁ [Term| if ‹c₁› then ‹t› else ‹f›] [Term| if ‹c₂› then ‹t› else ‹f›]

      -- | bind {ι: String} {τy: Ty} {expr: Term} {scope: Term} (h: IsValue expr): Eval₁ (.bind ι τ expr scope) ([ι ↦  expr] scope)
      -- | bindExpr {ι: String} {τy: Ty} {e₁ e₂: Term} {scope: Term} (h: Eval₁ e₁ e₂): Eval₁ (.bind ι τ e₁ scope) (.bind ι τ e₂ scope)

      -- TODO: Application
      -- | app {params: ParamList} {body: Term} {fn: Term} {args: ArgList ρ} (h₁: IsValue fn) (h₂: List.foldl (fun p t => p ∧ IsValue t) true args): Eval₁ (.app (.abs params body) args) (List.foldl (fun body (formal, arg) => [formal ↦ arg] body) body (List.zip (List.map fst formals) args))
      -- | appArgs {fn: Term} {args: ArgList} (h₁: IsValue fn)
      -- | appFn {fn₁ fn₂: Term} {args: ArgList ρ} (h: Eval₁ fn₁ fn₂): Eval₁ (.app fn₁ args) (.app fn₂ args)

    def Eval := RTC Eval₁
  end Term

  namespace Top
    inductive IsValue: Top → Prop where
    inductive HasType: Top → Ty → Prop where
    inductive Eval₁: Top → Top → Prop where
    def Eval := RTC Eval₁
  end Top

  namespace UnOp
    @[reducible]
    def Halts (op: UnOp) (t₁: Term): Prop := ∃ t₂: Term, Eval₁ op t₁ t₂ ∧ Term.IsValue t₂

    @[reducible]
    def Total (τ₁ τ₂: Ty) (op: UnOp) (t: Term): Prop :=
      (HasType op τ₁ τ₂) ∧ (Halts op t) ∧ True

    namespace Total
      theorem halts {τ₁ τ₂: Ty} {op: UnOp} {t: Term}: Total τ₁ τ₂ op t → Halts op t
        | ⟨_, hh, _⟩ => hh
    end Total
  end UnOp

  namespace BinOp
    @[reducible]
    def Halts (op: BinOp) (t₁ t₂: Term): Prop := ∃ t₃: Term, Eval₁ op t₁ t₂ t₃ ∧ Term.IsValue t₃

    @[reducible]
    def Total (τ₁ τ₂ τ₃: Ty) (op: BinOp) (t₁ t₂: Term): Prop :=
      (HasType op τ₁ τ₂ τ₃) ∧ (Halts op t₁ t₂) ∧ True

    namespace Total
      theorem halts {τ₁ τ₂ τ₃: Ty} {op: BinOp} {t₁ t₂: Term}: Total τ₁ τ₂ τ₃ op t₁ t₂ → Halts op t₁ t₂
        | ⟨_, hh, _⟩ => hh
    end Total
  end BinOp

  namespace Term
    @[reducible]
    def Halts (t₁: Term): Prop := ∃ t₂: Term, Eval t₁ t₂ ∧ IsValue t₂

    @[reducible]
    def Total (τ: Ty) (t: Term): Prop :=
      (HasType t τ) ∧ (Halts t) ∧ (
        match τ with
          | .bool => True
          | .nat  => True
      )

    namespace IsValue
      theorem halts {t: Term}: IsValue t → Halts t
        | .bool _ => ⟨_, .refl, .bool _⟩
        | .nat  _ => ⟨_, .refl, .nat  _⟩
    end IsValue

    namespace Total
      theorem halts {τ: Ty}: {t: Term} → Total τ t → Halts t
        | .bool _, _ => IsValue.halts (.bool _)
        | .nat _,  _ => IsValue.halts (.nat  _)

        | .unOp _ _,    ⟨_, ⟨_, he, hv⟩, _⟩
        | .binOp _ _ _, ⟨_, ⟨_, he, hv⟩, _⟩

        | .cond _ _ _,  ⟨_, ⟨_, he, hv⟩, _⟩ => ⟨_, he, hv⟩
    end Total
  end Term

  namespace Top
    @[reducible]
    def Halts (t₁: Top): Prop := ∃ t₂: Top, Eval t₁ t₂ ∧ IsValue t₂

    @[reducible]
    def Total: Ty → Top → Prop
      | .bool, t => nomatch t

    namespace IsValue
      theorem halts {t: Top}: IsValue t → Halts t := nomatch t
    end IsValue

    namespace Total
      theorem halts {τ: Ty} {t: Top}: Top → Halts t
        | t => nomatch t
    end Total
  end Top
end Total.Stlc.Lang.Surface
