import Total.Stlc.Lang.Surface.Grammar

namespace Total.Stlc.Lang.Surface
  declare_syntax_cat stlc_surface_ty
  declare_syntax_cat stlc_surface_tm
  declare_syntax_cat stlc_surface_top

  section Types
    scoped syntax "[Ty|" stlc_surface_ty "]" : term

    section Inject
      scoped syntax "‹" term "›" : stlc_surface_ty
      scoped syntax "(" stlc_surface_ty ")" : stlc_surface_ty

      macro_rules
        | `([Ty| ‹ $t:term › ])            => `($(Lean.quote t))
        | `([Ty| ( $t:stlc_surface_ty ) ]) => `([Ty| $t])

      example (t: Ty): [Ty| ‹t› ]   = t := rfl
      example (t: Ty): [Ty| (‹t›) ] = t := rfl
    end Inject

    section Booleans
      scoped syntax "𝔹" : stlc_surface_ty

      macro_rules
        | `([Ty| 𝔹 ]) => `(Ty.bool)

      example: [Ty| 𝔹] = .bool := rfl
    end Booleans

    section Nats
      scoped syntax "ℕ" : stlc_surface_ty

      macro_rules
        | `([Ty| ℕ ]) => `(Ty.nat)

      example: [Ty| ℕ] = .nat := rfl
    end Nats

    section Functions
      /-
      scoped syntax:30 stlc_surface_ty:31 "→" stlc_surface_ty:30 : stlc_surface_ty

      @[reducible]
      def fn: Ty → Ty → Ty
        | τ, .fn params res => .fn (τ :: params) res
        | τ₁, τ₂            => .fn [τ₁] τ₂

      macro_rules
        | `([Ty| $x:stlc_surface_ty → $y:stlc_surface_ty ]) => `(fn [Ty| $x] [Ty| $y])

      variable {τ₁ τ₂ τ₃: Ty}

      example: [Ty| ‹τ₁› → ‹τ₂› → ‹τ₃›]   = .fn [τ₁] τ₃          := sorry -- rfl
      example: [Ty| (‹τ₁› → ‹τ₂›) → ‹τ₃›] = .fn [.fn [τ₁] τ₂] τ₃ := sorry -- rfl
      -/
    end Functions
  end Types

  section Terms
    scoped syntax "[Term|" stlc_surface_tm "]" : term

    section Inject
      scoped syntax "‹" term "›" : stlc_surface_tm
      scoped syntax "(" stlc_surface_tm ")" : stlc_surface_tm

      macro_rules
        | `([Term| ‹ $t:term › ])            => `($(Lean.quote t))
        | `([Term| ( $t:stlc_surface_tm ) ]) => `([Term| $t])

      variable {v: Value}
      variable {t: Term}

      example: [Term| ‹t›]        = t := rfl
      example: [Term| (‹t›)]      = t := rfl
    end Inject

    section Booleans
      scoped syntax "tru" : stlc_surface_tm
      scoped syntax "fls" : stlc_surface_tm
      scoped syntax "‹bool:" term "›" : stlc_surface_tm

      macro_rules
        | `([Term| tru ])              => `(Term.bool true)
        | `([Term| fls ])              => `(Term.bool false)
        | `([Term| ‹bool: $b:term › ]) => `(Term.bool $(Lean.quote b))

      example: [Term| tru]      = @Term.bool true  := rfl
      example: [Term| fls]      = @Term.bool false := rfl
      example: [Term| ‹bool:b›] = @Term.bool b     := rfl
    end Booleans

    section Nats
      scoped syntax num : stlc_surface_tm
      scoped syntax "‹nat:" term "›" : stlc_surface_tm

      macro_rules
        | `([Term| $n:num ])          => `(Term.nat $n)
        | `([Term| ‹nat: $n:term › ]) => `(Term.nat $(Lean.quote n))

      example: [Term| 0]       = @Term.nat 0 := rfl
      example: [Term| 1]       = @Term.nat 1 := rfl
      example: [Term| 2]       = @Term.nat 2 := rfl
      example: [Term| ‹nat:n›] = @Term.nat n := rfl
    end Nats

    section Equality
      scoped syntax stlc_surface_tm "=" stlc_surface_tm : stlc_surface_tm
      scoped syntax stlc_surface_tm "≠" stlc_surface_tm : stlc_surface_tm

      macro_rules
        | `([Term| $lhs:stlc_surface_tm = $rhs:stlc_surface_tm]) => `(Term.eq  [Term| $lhs] [Term| $rhs])
        | `([Term| $lhs:stlc_surface_tm ≠ $rhs:stlc_surface_tm]) => `(Term.neq [Term| $lhs] [Term| $rhs])

      variable {t₁ t₂: Term}

      example: [Term| ‹t₁› = ‹t₂›] = .eq  t₁ t₂ := rfl
      example: [Term| ‹t₁› ≠ ‹t₂›] = .neq t₁ t₂ := rfl
    end Equality

    section Logic
      scoped syntax:30 stlc_surface_tm:30 "∨" stlc_surface_tm:31 : stlc_surface_tm
      scoped syntax:40 stlc_surface_tm:40 "∧" stlc_surface_tm:41 : stlc_surface_tm
      scoped syntax:max "¬" stlc_surface_tm:max : stlc_surface_tm

      macro_rules
        | `([Term| $lhs:stlc_surface_tm ∧ $rhs:stlc_surface_tm ]) => `(Term.and [Term| $lhs] [Term| $rhs])
        | `([Term| $lhs:stlc_surface_tm ∨ $rhs:stlc_surface_tm ]) => `(Term.or  [Term| $lhs] [Term| $rhs])
        | `([Term| ¬ $op:stlc_surface_tm ])                       => `(Term.not [Term| $op])

      variable {t t₁ t₂ t₃ t₄: Term}

      example: [Term| ‹t₁› ∧ ‹t₂›] = .and t₁ t₂ := rfl
      example: [Term| ‹t₁› ∨ ‹t₂›] = .or  t₁ t₂ := rfl
      example: [Term| ¬‹t›]        = .not t     := rfl

      example: [Term| ‹t₁› ∧ ‹t₂› ∧ ‹t₃›]   = .and (.and t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› ∧ ‹t₂›) ∧ ‹t₃›] = .and (.and t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› ∧ (‹t₂› ∧ ‹t₃›)] = .and t₁ (.and t₂ t₃) := rfl
      example: [Term| ‹t₁› ∨ ‹t₂› ∨ ‹t₃›]   = .or  (.or  t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› ∨ ‹t₂›) ∨ ‹t₃›] = .or  (.or  t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› ∨ (‹t₂› ∨ ‹t₃›)] = .or  t₁ (.or  t₂ t₃) := rfl

      example: [Term| ¬‹t₁› ∧ ‹t₂›]   = .and (.not t₁) t₂ := rfl
      example: [Term| ‹t₁› ∧ ¬‹t₂›]   = .and t₁ (.not t₂) := rfl
      example: [Term| ¬‹t₁› ∨ ‹t₂›]   = .or  (.not t₁) t₂ := rfl
      example: [Term| ‹t₁› ∨ ¬‹t₂›]   = .or  t₁ (.not t₂) := rfl
      example: [Term| ¬(‹t₁› ∧ ‹t₂›)] = .not (.and t₁ t₂) := rfl
      example: [Term| ¬(‹t₁› ∨ ‹t₂›)] = .not (.or  t₁ t₂) := rfl

      example: [Term| ‹t₁› ∧ ‹t₂› ∨ ‹t₃› ∧ ‹t₄›] = .or (.and t₁ t₂) (.and t₃ t₄) := rfl
    end Logic

    section Arithmetic
      scoped syntax:60 stlc_surface_tm:60 "+" stlc_surface_tm:61 : stlc_surface_tm
      scoped syntax:70 stlc_surface_tm:70 "*" stlc_surface_tm:71 : stlc_surface_tm

      macro_rules
        | `([Term| $lhs:stlc_surface_tm + $rhs:stlc_surface_tm ]) => `(Term.add [Term| $lhs] [Term| $rhs])
        | `([Term| $lhs:stlc_surface_tm * $rhs:stlc_surface_tm ]) => `(Term.mul [Term| $lhs] [Term| $rhs])

      variable {lhs rhs t₁ t₂ t₃ t₄: Term}

      example: [Term| ‹lhs› + ‹rhs›] = .add lhs rhs := rfl
      example: [Term| ‹lhs› * ‹rhs›] = .mul lhs rhs := rfl

      example: [Term| ‹t₁› + ‹t₂› + ‹t₃›]   = .add (.add t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› + ‹t₂›) + ‹t₃›] = .add (.add t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› + (‹t₂› + ‹t₃›)] = .add t₁ (.add t₂ t₃) := rfl
      example: [Term| ‹t₁› * ‹t₂› * ‹t₃›]   = .mul (.mul t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› * ‹t₂›) * ‹t₃›] = .mul (.mul t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› * (‹t₂› * ‹t₃›)] = .mul t₁ (.mul t₂ t₃) := rfl

      example: [Term| ‹t₁› + ‹t₂› * ‹t₃›] = .add t₁ (.mul t₂ t₃) := rfl
      example: [Term| ‹t₁› * ‹t₂› + ‹t₃›] = .add (.mul t₁ t₂) t₃ := rfl

      example: [Term| ‹t₁› * ‹t₂› + ‹t₃› * ‹t₄›] = .add (.mul t₁ t₂) (.mul t₃ t₄) := rfl
    end Arithmetic

    section Comparison
      scoped syntax:50 stlc_surface_tm:50 "<" stlc_surface_tm:50 : stlc_surface_tm
      scoped syntax:50 stlc_surface_tm:50 "≤" stlc_surface_tm:50 : stlc_surface_tm
      scoped syntax:50 stlc_surface_tm:50 ">" stlc_surface_tm:50 : stlc_surface_tm
      scoped syntax:50 stlc_surface_tm:50 "≥" stlc_surface_tm:50 : stlc_surface_tm

      macro_rules
        | `([Term| $lhs:stlc_surface_tm < $rhs:stlc_surface_tm]) => `(Term.lt  [Term| $lhs] [Term| $rhs])
        | `([Term| $lhs:stlc_surface_tm ≤ $rhs:stlc_surface_tm]) => `(Term.lte [Term| $lhs] [Term| $rhs])
        | `([Term| $lhs:stlc_surface_tm > $rhs:stlc_surface_tm]) => `(Term.gt  [Term| $lhs] [Term| $rhs])
        | `([Term| $lhs:stlc_surface_tm ≥ $rhs:stlc_surface_tm]) => `(Term.gte [Term| $lhs] [Term| $rhs])

      variable {lhs rhs: Term}

      example: [Term| ‹lhs› < ‹rhs›] = .lt  lhs rhs := rfl
      example: [Term| ‹lhs› ≤ ‹rhs›] = .lte lhs rhs := rfl
      example: [Term| ‹lhs› > ‹rhs›] = .gt  lhs rhs := rfl
      example: [Term| ‹lhs› ≥ ‹rhs›] = .gte lhs rhs := rfl
    end Comparison

    section Conditionals
      scoped syntax "if" stlc_surface_tm "then" stlc_surface_tm "else" stlc_surface_tm : stlc_surface_tm

      macro_rules
        | `([Term| if $c:stlc_surface_tm then $t:stlc_surface_tm else $f:stlc_surface_tm ]) => `(Term.cond [Term| $c] [Term| $t] [Term| $f])

      variable {c t f: Term}

      example: [Term| if ‹c› then ‹t› else ‹f›] = .cond c t f := rfl
    end Conditionals

    section Bindings
    end Bindings

    section Functions
    end Functions
  end Terms

  section TopLevel
    scoped syntax "[Top|" stlc_surface_top "]" : term

    section Inject
      scoped syntax "‹" term "›" : stlc_surface_top

      macro_rules
        | `([Top| ‹ $t:term › ]) => `($(Lean.quote t))

      variable {t: Top}

      example: [Top| ‹t›] = t := rfl
    end Inject

    section Types
    end Types

    section Values
    end Values

    section Definitions
    end Definitions

    section Implementations
    end Implementations
  end TopLevel
end Total.Stlc.Lang.Surface
