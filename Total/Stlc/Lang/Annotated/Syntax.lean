import Total.Core

import Total.Stlc.Lang.Annotated.Grammar

set_option autoImplicit false

namespace Total.Stlc.Lang.Annotated
  declare_syntax_cat stlc_annot_ty
  declare_syntax_cat stlc_term_ty
  declare_syntax_cat stlc_top_ty

  section Types
    scoped syntax "[Ty|" stlc_annot_ty "]" : term

    section Inject
      scoped syntax "‹" term "›" : stlc_annot_ty
      scoped syntax "(" stlc_annot_ty ")" : stlc_annot_ty

      macro_rules
        | `([Ty| ‹ $t:term › ])          => `($(Lean.quote t))
        | `([Ty| ( $t:stlc_annot_ty ) ]) => `([Ty| $t])

      variable {t: Ty}

      example: [Ty| ‹t›]   = t := rfl
      example: [Ty| (‹t›)] = t := rfl
    end Inject

    section Booleans
      scoped syntax "𝔹" : stlc_annot_ty

      macro_rules
        | `([Ty| 𝔹]) => `(Ty.bool)

      example: [Ty| 𝔹] = .bool := rfl
    end Booleans

    section Nats
      scoped syntax "ℕ" : stlc_annot_ty

      macro_rules
        | `([Ty| ℕ]) => `(Ty.nat)

      example: [Ty| ℕ] = .nat := rfl
    end Nats

    section Functions
      /-
      scoped syntax "⟨" stlc_annot_ty,* "⟩" "→" stlc_annot_ty : stlc_annot_ty

      private def toParams: (tys: List (Lean.TSyntax `stlc_annot_ty)) → Params Ty tys.length
        | []  => .nil
        | ty :: tys => .cons `([Ty| $ty]) (toParams tys)

      macro_rules
        | `([Ty| ⟨ $dom:stlc_annot_ty,* ⟩ → $rng:stlc_annot_ty ]) =>
          let params := toParams dom.getElems.toList
          let r := `([Ty| $rng])
          let f := Ty.fn params r
          `($f)
        -- )
        --     let dom₁ := dom.getElems
        --     let dom₂ := dom₁.toList
        --     let rng₁ := $(Lean.quote rng)
        --     .nat
        --   --   let tys := (Lean.quote dom).getElems.map (fun x => x)
        --   --   tys
        --   -- -- fn (toParams (dom.getElems.toList.map (fun x => x [Ty| $x]))) [Ty| $rng]
        -- )

      variable {τ₁ τ₂ τ₃: Ty}

      example: [Ty| ⟨ℕ, ℕ⟩ → 𝔹]   = .fn (.cons τ₁ (.cons τ₂ .nil)) τ₃            := rfl
      example: [Ty| ⟨⟨‹τ₁›⟩ → ‹τ₂›⟩ → ‹τ₃›] = .fn (.cons (.fn (.cons τ₁ .nil) τ₂) .nil) τ₃ := rfl
      -/
    end Functions
  end Types
end Total.Stlc.Lang.Annotated
