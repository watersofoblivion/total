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

    inductive HasType: Env → Term → Ty → Prop where
      | bool {ε: Env} {b: Bool}: HasType ε [Term| ‹bool:b›] [Ty| 𝔹]
      | nat {ε: Env} {n: Nat}: HasType ε [Term| ‹nat:n›] [Ty| ℕ]
      | and {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| 𝔹]) (h₂: HasType ε rhs [Ty| 𝔹]): HasType ε [Term| ‹lhs› ∧ ‹rhs›] [Ty| 𝔹]
      | or  {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| 𝔹]) (h₂: HasType ε rhs [Ty| 𝔹]): HasType ε [Term| ‹lhs› ∨ ‹rhs›] [Ty| 𝔹]
      | not {ε: Env} {op: Term} (h: HasType ε op [Ty| 𝔹]): HasType ε [Term| ¬ ‹op›] [Ty| 𝔹]
      | add {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| ℕ]) (h₂: HasType ε rhs [Ty| ℕ]): HasType ε [Term| ‹lhs› + ‹rhs›] [Ty| ℕ]
      | sub {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| ℕ]) (h₂: HasType ε rhs [Ty| ℕ]): HasType ε [Term| ‹lhs› - ‹rhs›] [Ty| ℕ]
      | mul {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| ℕ]) (h₂: HasType ε rhs [Ty| ℕ]): HasType ε [Term| ‹lhs› * ‹rhs›] [Ty| ℕ]
      | eq  {ε: Env} {lhs rhs: Term} {τ: Ty} (h₁: HasType ε lhs τ) (h₂: HasType ε rhs τ): HasType ε [Term| ‹lhs› = ‹rhs›] [Ty| 𝔹]
      | neq {ε: Env} {lhs rhs: Term} {τ: Ty} (h₁: HasType ε lhs τ) (h₂: HasType ε rhs τ): HasType ε [Term| ‹lhs› ≠ ‹rhs›] [Ty| 𝔹]
      | lt  {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| ℕ]) (h₂: HasType ε rhs [Ty| ℕ]): HasType ε [Term| ‹lhs› < ‹rhs›] [Ty| 𝔹]
      | lte {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| ℕ]) (h₂: HasType ε rhs [Ty| ℕ]): HasType ε [Term| ‹lhs› ≤ ‹rhs›] [Ty| 𝔹]
      | gt  {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| ℕ]) (h₂: HasType ε rhs [Ty| ℕ]): HasType ε [Term| ‹lhs› < ‹rhs›] [Ty| 𝔹]
      | gte {ε: Env} {lhs rhs: Term} (h₁: HasType ε lhs [Ty| ℕ]) (h₂: HasType ε rhs [Ty| ℕ]): HasType ε [Term| ‹lhs› ≤ ‹rhs›] [Ty| 𝔹]
      | cond {ε: Env} {c t f: Term} {τ: Ty} (h₁: HasType ε c [Ty| 𝔹]) (h₂: HasType ε t τ) (h₃: HasType ε f τ): HasType ε [Term| if ‹c› then ‹t› else ‹f›] τ
      -- | var  {ε: Env} {τ: Ty}: HasType ε _ τ
      -- | bind {ε: Env} {expr scope: Term} {τ₁ τ₂: Ty} (h₁: HasType ε expr τ₁) (h₂: HasType (ε.bind ι τ₁) scope τ₂): HasType ε (.bind t₁ expr scope) τ₂
      -- TODO: Turn List.{foldl,map} applications into functions on FormalList
      -- | abs {ε: Env} {formals: FormalList} {body: Term} {τ: Ty} (h: HasType (List.foldl (fun ε (ι, τ) => ε.bind ι τ) ε formals) body τ): HasType ε (.abs formals body) (.fn (List.map (·.snd) formals) τ)
      -- TODO: Turn List.{foldl,zip} applications into functions on FormalList
      -- ERROR: Free Variable Somewhere?!?!
      -- | app {ε: Env} {params: ParamList} {res: Ty} {fn: Term} {args: ArgList} (h₁: HasType ε fn (.fn params res)) (h₂: List.foldl (fun p (t, τ) => p ∧ HasType ε t τ) true (List.zip args params)): HasType ε (.app fn args) res

    inductive Eval₁: Term → Term → Prop where
      | and {lhs rhs: Bool}: Eval₁ [Term| ‹bool:lhs› ∧ ‹bool:rhs›] [Term| ‹bool:lhs && rhs›]
      | andRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› ∧ ‹rhs₁›] [Term| ‹lhs› ∧ ‹rhs₂›]
      | andLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› ∧ ‹rhs›] [Term| ‹lhs₂› ∧ ‹rhs›]

      | or {lhs rhs: Bool}: Eval₁ [Term| ‹bool:lhs› ∨ ‹bool:rhs›] [Term| ‹bool:lhs || rhs›]
      | orRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› ∨ ‹rhs₁›] [Term| ‹lhs› ∨ ‹rhs₂›]
      | orLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› ∨ ‹rhs›] [Term| ‹lhs₂› ∨ ‹rhs›]

      | not {op: Bool}: Eval₁ [Term| ¬ ‹bool:op›] [Term| ‹bool:!op›]
      | notOp {op₁ op₂: Term} (h: Eval₁ op₁ op₂): Eval₁ [Term| ¬ ‹op₁›] [Term| ‹op₂›]

      | add {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› + ‹nat:rhs›] [Term| ‹nat:lhs + rhs›]
      | addRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› + ‹rhs₁›] [Term| ‹lhs› + ‹rhs₂›]
      | addLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› + ‹rhs›] [Term| ‹lhs₂› + ‹rhs›]

      | sub {lhs rhs: Nat}: Eval₁ [Term| ‹nat:lhs› - ‹nat:rhs›] [Term| ‹nat:lhs - rhs›]
      | subRight {lhs rhs₁ rhs₂: Term} (h₁: IsValue lhs) (h₂: Eval₁ rhs₁ rhs₂): Eval₁ [Term| ‹lhs› - ‹rhs₁›] [Term| ‹lhs› - ‹rhs₂›]
      | subLeft {lhs₁ lhs₂ rhs: Term} (h: Eval₁ lhs₁ lhs₂): Eval₁ [Term| ‹lhs₁› - ‹rhs›] [Term| ‹lhs₂› - ‹rhs›]

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
      | contFalse {t f: Term}: Eval₁ [Term| if fls then ‹t› else ‹f›] [Term| ‹f›]
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
