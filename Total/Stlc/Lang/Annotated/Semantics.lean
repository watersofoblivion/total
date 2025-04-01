import Total.Core
import Total.Relation

import Total.Stlc.Lang.Annotated.Grammar
import Total.Stlc.Lang.Annotated.Syntax

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  namespace PrimOp
    inductive Eval₁: {α: Nat} → {δ: Domain α} → {τ: Ty} → PrimOp δ τ → Values δ → Term τ → Prop where
      | and {lhs rhs: Bool} (vs: Values (.cons .bool (.nil .bool))): Eval₁ .and (.cons (.bool lhs) (.nil (.bool rhs))) (.value (.bool (lhs && rhs)))
      | or  {lhs rhs: Bool} (vs: Values (.cons .bool (.nil .bool))): Eval₁ .or  (.cons (.bool lhs) (.nil (.bool rhs))) (.value (.bool (lhs || rhs)))
      | not {operand: Bool} (vs: Values (.nil .bool)): Eval₁ .not (.nil (.bool operand)) (.value (.bool (!operand)))

      | add {lhs rhs: Nat} (vs: Values (.cons .nat (.nil .nat))): Eval₁ .add (.cons (.nat lhs) (.nil (.nat rhs))) (.value (.nat (lhs + rhs)))
      | mul {lhs rhs: Nat} (vs: Values (.cons .nat (.nil .nat))): Eval₁ .mul (.cons (.nat lhs) (.nil (.nat rhs))) (.value (.nat (lhs * rhs)))

      | eqBool  {lhs rhs: Bool} (vs: Values (.cons .bool (.nil .bool))): Eval₁ .eq  (.cons (.bool lhs) (.nil (.bool rhs))) (.value (.bool (lhs == rhs)))
      | eqNat   {lhs rhs: Nat}  (vs: Values (.cons .nat  (.nil .nat))):  Eval₁ .eq  (.cons (.nat  lhs) (.nil (.nat  rhs))) (.value (.bool (lhs == rhs)))
      | neqBool {lhs rhs: Bool} (vs: Values (.cons .bool (.nil .bool))): Eval₁ .neq (.cons (.bool lhs) (.nil (.bool rhs))) (.value (.bool (lhs != rhs)))
      | neqNat  {lhs rhs: Nat}  (vs: Values (.cons .nat  (.nil .nat))):  Eval₁ .neq (.cons (.nat  lhs) (.nil (.nat  rhs))) (.value (.bool (lhs != rhs)))

      | lt  {lhs rhs: Nat} (vs: Values (.cons .nat (.nil .nat))): Eval₁ .lt  (.cons (.nat lhs) (.nil (.nat rhs))) (.value (.bool (lhs < rhs)))
      | lte {lhs rhs: Nat} (vs: Values (.cons .nat (.nil .nat))): Eval₁ .lte (.cons (.nat lhs) (.nil (.nat rhs))) (.value (.bool (lhs ≤ rhs)))
      | gt  {lhs rhs: Nat} (vs: Values (.cons .nat (.nil .nat))): Eval₁ .gt  (.cons (.nat lhs) (.nil (.nat rhs))) (.value (.bool (lhs > rhs)))
      | gte {lhs rhs: Nat} (vs: Values (.cons .nat (.nil .nat))): Eval₁ .gte (.cons (.nat lhs) (.nil (.nat rhs))) (.value (.bool (lhs ≥ rhs)))
  end PrimOp

  namespace Value
    inductive IsValue: {τ: Ty} → Value τ → Prop where
      | bool (b: Bool): IsValue (.bool b)
      | nat  (n: Nat):  IsValue (.nat n)
  end Value

  mutual
    inductive Term.Eval₁: {τ: Ty} → Term τ → Term τ → Prop where
      | primOpArgs {α: Nat} {δ: Domain α} {τ ρ: Ty} {op: PrimOp δ ρ} {args₁ args₂: Args δ} (h: Args.Eval₁ args₁ args₂): Term.Eval₁ (.primOp op args₁) (.primOp op args₂)
      | primOp {α: Nat} {δ: Domain α} {ρ: Ty} {op: PrimOp δ ρ} {vs: Values δ} {res: Term ρ} (h: PrimOp.Eval₁ op vs res): Term.Eval₁ (.primOp op (.values vs)) res
      | condTrue {τ: Ty} {t f: Term τ}: Term.Eval₁ (.cond (.value (.bool true)) t f) t
      | condFalse {τ: Ty} {t f: Term τ}: Term.Eval₁ (.cond (.value (.bool false)) t f) f
      | cond {τ: Ty} {c₁ c₂: Term .bool} {t f: Term τ} (h: Term.Eval₁ c₁ c₂): Term.Eval₁ (.cond c₁ t f) (.cond c₂ t f)

    inductive Args.Eval₁: {α: Nat} → {δ: Domain α} → Args δ → Args δ → Prop where
      | nil {α: Nat} {δ: Domain α} {vs: Values δ} {τ: Ty} {t₁ t₂: Term τ} (h: Term.Eval₁ t₁ t₂): Args.Eval₁ (.mix vs (.nil t₁)) (.mix vs (.nil t₂))
      | nilValue {α: Nat} {δ: Domain α} {vs: Values δ} {τ: Ty} {v: Value τ}: Args.Eval₁ (.mix vs (.nil (.value v))) (.values (vs ++ (Values.nil v)))
      | cons {α β: Nat} {δ₁: Domain α} {δ₂: Domain β} {vs: Values δ₁} {τ: Ty} {t₁ t₂: Term τ} {ts: Terms δ₂} (h: Term.Eval₁ t₁ t₂): Args.Eval₁ (.mix vs (.cons t₁ ts)) (.mix vs (.cons t₂ ts))
      -- | consValue {α β: Nat} {δ₁: Domain α} {δ₂: Domain β} {τ: Ty} {vs: Values δ₁} {v: Value τ} {ts: Terms δ₂}: Args.Eval₁ (.mix vs (.cons (.value v) ts)) (.mix (vs ++ v) ts)
  end

  namespace Term
    inductive IsValue: {τ: Ty} → Term τ → Prop where
      | value {τ: Ty} (v: Value τ): IsValue (.value v)

    abbrev Eval {τ: Ty}: Term τ → Term τ → Prop := RTC Eval₁
  end Term

  namespace Args
    inductive IsValue: {α: Nat} → {δ: Domain α} → Args δ → Prop where
      | values {α: Nat} {δ: Domain α} (vs: Values δ): IsValue (.values vs)

    abbrev Eval {α: Nat} {δ: Domain α}: Args δ → Args δ → Prop := RTC Eval₁
  end Args

  namespace Top
    inductive IsValue: {τ: Ty} → Top τ → Prop where
    inductive Eval₁: {τ: Ty} → Top τ → Top τ → Prop where
    abbrev Eval {τ: Ty}: Top τ → Top τ → Prop := RTC Eval₁
  end Top
end Total.Stlc.Lang.Annotated
