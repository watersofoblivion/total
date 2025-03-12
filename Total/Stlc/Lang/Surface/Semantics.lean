import Total.Relation

import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax

namespace Total.Stlc.Lang.Surface
  section Types
  end Types

  namespace Term
    inductive IsValue: Term → Prop where
      | bool (b: Bool): IsValue [Term| ‹bool:b›]
      | nat (n: Nat): IsValue [Term| ‹nat:n›]
      -- | var (id: String): IsValue (.var id)
      -- | abs (params: List (String × Ty)) (body: Term): IsValue (.abs params body)

    inductive HasType: Term → Ty → Prop where
      | bool {b: Bool}: HasType [Term| ‹bool:b›] [Ty| 𝔹]
      | nat {n: Nat}: HasType [Term| ‹nat:n›] [Ty| ℕ]
      | and {lhs rhs: Term} (h₁: HasType lhs [Ty| 𝔹]) (h₂: HasType rhs [Ty| 𝔹]): HasType [Term| ‹lhs› ∧ ‹rhs›] [Ty| 𝔹]
      | or  {lhs rhs: Term} (h₁: HasType lhs [Ty| 𝔹]) (h₂: HasType rhs [Ty| 𝔹]): HasType [Term| ‹lhs› ∨ ‹rhs›] [Ty| 𝔹]
      | not {op: Term} (h: HasType op [Ty| 𝔹]): HasType [Term| ¬ ‹op›] [Ty| 𝔹]
      | add {lhs rhs: Term} (h₁: HasType lhs [Ty| ℕ]) (h₂: HasType rhs [Ty| ℕ]): HasType [Term| ‹lhs› + ‹rhs›] [Ty| ℕ]
      | mul {lhs rhs: Term} (h₁: HasType lhs [Ty| ℕ]) (h₂: HasType rhs [Ty| ℕ]): HasType [Term| ‹lhs› * ‹rhs›] [Ty| ℕ]
      | eq  {lhs rhs: Term} {τ: Ty} (h₁: HasType lhs τ) (h₂: HasType rhs τ): HasType [Term| ‹lhs› = ‹rhs›] [Ty| 𝔹]
      | neq {lhs rhs: Term} {τ: Ty} (h₁: HasType lhs τ) (h₂: HasType rhs τ): HasType [Term| ‹lhs› ≠ ‹rhs›] [Ty| 𝔹]
      | lt  {lhs rhs: Term} (h₁: HasType lhs [Ty| ℕ]) (h₂: HasType rhs [Ty| ℕ]): HasType [Term| ‹lhs› < ‹rhs›] [Ty| 𝔹]
      | lte {lhs rhs: Term} (h₁: HasType lhs [Ty| ℕ]) (h₂: HasType rhs [Ty| ℕ]): HasType [Term| ‹lhs› ≤ ‹rhs›] [Ty| 𝔹]
      | gt  {lhs rhs: Term} (h₁: HasType lhs [Ty| ℕ]) (h₂: HasType rhs [Ty| ℕ]): HasType [Term| ‹lhs› > ‹rhs›] [Ty| 𝔹]
      | gte {lhs rhs: Term} (h₁: HasType lhs [Ty| ℕ]) (h₂: HasType rhs [Ty| ℕ]): HasType [Term| ‹lhs› ≥ ‹rhs›] [Ty| 𝔹]
      | cond {c t f: Term} {τ: Ty} (h₁: HasType c [Ty| 𝔹]) (h₂: HasType t τ) (h₃: HasType f τ): HasType [Term| if ‹c› then ‹t› else ‹f›] τ
      -- | var  {τ: Ty}: HasType _ τ
      -- | bind {expr scope: Term} {τ₁ τ₂: Ty} (h₁: HasType expr τ₁) (h₂: HasType (ε.bind ι τ₁) scope τ₂): HasType (.bind t₁ expr scope) τ₂
      -- TODO: Turn List.{foldl,map} applications into functions on FormalList
      -- | abs {formals: FormalList} {body: Term} {τ: Ty} (h: HasType (List.foldl (fun ε (ι, τ) => ε.bind ι τ) ε formals) body τ): HasType (.abs formals body) (.fn (List.map (·.snd) formals) τ)
      -- TODO: Turn List.{foldl,zip} applications into functions on FormalList
      -- ERROR: Free Variable Somewhere?!?!
      -- | app {params: ParamList} {res: Ty} {fn: Term} {args: ArgList} (h₁: HasType fn (.fn params res)) (h₂: List.foldl (fun p (t, τ) => p ∧ HasType t τ) true (List.zip args params)): HasType (.app fn args) res

    inductive Eval₁: Term → Term → Prop where
      | and {lhs rhs: Bool}: Eval₁ [Term| ‹bool:lhs› ∧ ‹bool:rhs›] [Term| ‹bool:lhs && rhs›]
      | andRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› ∧ ‹rhs₁›] [Term| ‹lhs› ∧ ‹rhs₂›]
      | andLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› ∧ ‹rhs›] [Term| ‹lhs₂› ∧ ‹rhs›]

      | or {lhs rhs: Bool}: Eval₁ [Term| ‹bool:lhs› ∨ ‹bool:rhs›] [Term| ‹bool:lhs || rhs›]
      | orRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› ∨ ‹rhs₁›] [Term| ‹lhs› ∨ ‹rhs₂›]
      | orLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› ∨ ‹rhs›] [Term| ‹lhs₂› ∨ ‹rhs›]

      | not {op: Bool}: Eval₁ [Term| ¬ ‹bool:op›] [Term| ‹bool:!op›]
      | notOp {op₁ op₂: Term} (h: Eval₁ op₁ op₂): Eval₁ [Term| ¬‹op₁›] [Term| ‹op₂›]

      | add {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› + ‹nat:rhs›] [Term| ‹nat:lhs + rhs›]
      | addRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› + ‹rhs₁›] [Term| ‹lhs› + ‹rhs₂›]
      | addLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› + ‹rhs›] [Term| ‹lhs₂› + ‹rhs›]

      | mul {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› * ‹nat:rhs›] [Term| ‹nat:lhs * rhs›]
      | mulRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› * ‹rhs₁›] [Term| ‹lhs› * ‹rhs₂›]
      | mulLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› * ‹rhs›] [Term| ‹lhs₂› * ‹rhs›]

      | eqBool {lhs rhs: Bool}: Eval₁ [Term| ‹bool:lhs› = ‹bool:rhs›] [Term| ‹bool:lhs == rhs›]
      | eqNat  {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› = ‹nat:rhs›] [Term| ‹bool:lhs == rhs›]
      | eqRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› = ‹rhs₁›] [Term| ‹lhs› = ‹rhs₂›]
      | eqLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› = ‹rhs›] [Term| ‹lhs₂› = ‹rhs›]

      | neqBool {lhs rhs: Bool}: Eval₁ [Term| ‹bool:lhs› ≠ ‹bool:rhs›] [Term| ‹bool:lhs != rhs›]
      | neqNat  {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› ≠ ‹nat:rhs›] [Term| ‹bool:lhs != rhs›]
      | neqRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› ≠ ‹rhs₁›] [Term| ‹lhs› ≠ ‹rhs₂›]
      | neqLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› ≠ ‹rhs›] [Term| ‹lhs₂› ≠ ‹rhs›]

      | lt {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› < ‹nat:rhs›] [Term| ‹bool:lhs < rhs›]
      | ltRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› < ‹rhs₁›] [Term| ‹lhs› < ‹rhs₂›]
      | ltLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› < ‹rhs›] [Term| ‹lhs₂› < ‹rhs›]

      | lte {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› ≤ ‹nat:rhs›] [Term| ‹bool:lhs ≤ rhs›]
      | lteRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› ≤ ‹rhs₁›] [Term| ‹lhs› ≤ ‹rhs₂›]
      | lteLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› ≤ ‹rhs›] [Term| ‹lhs₂› ≤ ‹rhs›]

      | gt {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› > ‹nat:rhs›] [Term| ‹bool:lhs > rhs›]
      | gtRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› > ‹rhs₁›] [Term| ‹lhs› > ‹rhs₂›]
      | gtLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› > ‹rhs›] [Term| ‹lhs₂› > ‹rhs›]

      | gte {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› ≥ ‹nat:rhs›] [Term| ‹bool:lhs ≥ rhs›]
      | gteRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› ≥ ‹rhs₁›] [Term| ‹lhs› ≥ ‹rhs₂›]
      | gteLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› ≥ ‹rhs›] [Term| ‹lhs₂› ≥ ‹rhs›]

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
end Total.Stlc.Lang.Surface
