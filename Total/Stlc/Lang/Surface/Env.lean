import Total.Stlc.Lang.Surface.Grammar
import Total.Stlc.Lang.Surface.Syntax

namespace Total.Stlc.Lang.Surface
  def Env: Type := String → Option Ty

  namespace Env
    def empty: Env
      | _ => .none

    @[reducible]
    def bind (env: Env) (ι₁: String) (τ: Ty): Env
      | ι₂ => if ι₁ = ι₂ then .some τ else env ι₂

    namespace bind
      @[simp]
      theorem empty {ι: String} {τ: Ty}: (Env.empty.bind ι τ ι) = .some τ := by
        unfold Env.bind
        simp

      @[simp]
      theorem eq {ε: Env} {ι: String} {τ: Ty}: (ε.bind ι τ ι) = .some τ := by
        unfold Env.bind
        simp

      @[simp]
      theorem neq {ε: Env} {ι₁ ι₂: String} {τ: Ty} {h: ι₁ ≠ ι₂}: (ε.bind ι₁ τ ι₂) = ε ι₂ := by
        unfold Env.bind
        simp [h]

      @[simp]
      theorem shadow {ε: Env} {ι: String} {τ₁ τ₂: Ty}: (ε.bind ι τ₁ |>.bind ι τ₂) ι = ε.bind ι τ₂ ι := by
        unfold Env.bind
        simp

      @[simp]
      theorem id {ε: Env} {ι: String} {τ: Ty} {h: ε ι = .some τ}: ε.bind ι τ = ε := by
        unfold Env.bind
        rw [← h]
        simp_all

      @[simp]
      theorem permute {ε: Env} {ι₁ ι₂: String} {τ₁ τ₂: Ty} {h: ι₁ ≠ ι₂}: (ε.bind ι₁ τ₁ |>.bind ι₂ τ₂) = (ε.bind ι₂ τ₂ |>.bind ι₁ τ₁) := by
        unfold Env.bind
        funext ι
        cases ι₁ == ι with
          | true =>
            cases ι₂ == ι with
              | true => simp; sorry --simp
              | false => simp; sorry --simp
          | false =>
            cases ι₂ == ι with
              | true => simp; sorry --simp
              | false => simp; sorry --simp
    end bind
  end Env

  declare_syntax_cat stlc_surface_env
  scoped syntax "[Env|" stlc_surface_env "]" : term

  scoped syntax "●" : stlc_surface_env
  scoped syntax stlc_surface_env ";" ident ":" stlc_surface_ty : stlc_surface_env

  macro_rules
    | `([Env| ● ])                                                   => `(Env.empty)
    | `([Env| $e:stlc_surface_env; $id:ident : $t:stlc_surface_ty ]) => `([Env| $e].bind $(Lean.quote (toString id)) [Ty| $t])
end Total.Stlc.Lang.Surface
