import Total.Stlc.Lang.Surface.Grammar

set_option autoImplicit false

namespace Total.Stlc.Lang.Surface
  /-!
  # Simply-Typed Lambda Calculus Surface Syntax Internal Syntax
  -/

  declare_syntax_cat stlc_surface_ty
  declare_syntax_cat stlc_surface_un_op
  declare_syntax_cat stlc_surface_bin_op
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

  section UnOps
    scoped syntax "[UnOp|" stlc_surface_un_op "]" : term

    scoped syntax "‹un:" term "›" : stlc_surface_un_op
    scoped syntax "¬" : stlc_surface_un_op

    macro_rules
      | `([UnOp| ‹un: $t:term › ]) => `($(Lean.quote t))
      | `([UnOp| ¬ ])              => `(UnOp.not)
  end UnOps

  section BinOps
    scoped syntax "[BinOp|" stlc_surface_bin_op "]" : term

    scoped syntax "‹bin:" term "›" : stlc_surface_bin_op
    scoped syntax "∧" : stlc_surface_bin_op
    scoped syntax "∨" : stlc_surface_bin_op
    scoped syntax "+" : stlc_surface_bin_op
    scoped syntax "*" : stlc_surface_bin_op
    scoped syntax "=" : stlc_surface_bin_op
    scoped syntax "≠" : stlc_surface_bin_op
    scoped syntax "<" : stlc_surface_bin_op
    scoped syntax "≤" : stlc_surface_bin_op
    scoped syntax ">" : stlc_surface_bin_op
    scoped syntax "≥" : stlc_surface_bin_op

    macro_rules
      | `([BinOp| ‹bin: $t:term › ]) => `($(Lean.quote t))
      | `([BinOp| ∧ ])               => `(BinOp.and)
      | `([BinOp| ∨ ])               => `(BinOp.or)
      | `([BinOp| + ])               => `(BinOp.add)
      | `([BinOp| * ])               => `(BinOp.mul)
      | `([BinOp| = ])               => `(BinOp.eq)
      | `([BinOp| ≠ ])               => `(BinOp.neq)
      | `([BinOp| < ])               => `(BinOp.lt)
      | `([BinOp| ≤ ])               => `(BinOp.lte)
      | `([BinOp| > ])               => `(BinOp.gt)
      | `([BinOp| ≥ ])               => `(BinOp.gte)
  end BinOps

  section Terms
    scoped syntax "[Term|" stlc_surface_tm "]" : term

    section Inject
      scoped syntax "‹" term "›" : stlc_surface_tm
      scoped syntax "(" stlc_surface_tm ")" : stlc_surface_tm

      macro_rules
        | `([Term| ‹ $t:term › ])            => `($(Lean.quote t))
        | `([Term| ( $t:stlc_surface_tm ) ]) => `([Term| $t])

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

      variable {b: Bool}

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

      variable {n: Nat}

      example: [Term| 0]       = @Term.nat 0 := rfl
      example: [Term| 1]       = @Term.nat 1 := rfl
      example: [Term| 2]       = @Term.nat 2 := rfl
      example: [Term| ‹nat:n›] = @Term.nat n := rfl
    end Nats

    section UnOp
      scoped syntax stlc_surface_un_op stlc_surface_tm : stlc_surface_tm

      macro_rules
        | `([Term| $op:stlc_surface_un_op $operand:stlc_surface_tm]) => `(Term.unOp [UnOp| $op] [Term| $operand])

      variable {op: UnOp}
      variable {t: Term}

      example: [Term| ‹un:op› ‹t›] = .unOp op t := rfl
    end UnOp

    section BinOp
      scoped syntax stlc_surface_tm stlc_surface_bin_op stlc_surface_tm : stlc_surface_tm

      macro_rules
        | `([Term| $lhs:stlc_surface_tm $op:stlc_surface_bin_op $rhs:stlc_surface_tm]) => `(Term.binOp [BinOp| $op] [Term| $lhs] [Term| $rhs])

      variable {op: BinOp}
      variable {t₁ t₂: Term}

      example: [Term| ‹t₁› ‹bin:op› ‹t₂›] = .binOp op t₁ t₂ := rfl
    end BinOp

    section Logic
      variable {t t₁ t₂ t₃ t₄: Term}

      example: [Term| ‹t₁› ∧ ‹t₂›] = .binOp .and t₁ t₂ := rfl
      example: [Term| ‹t₁› ∨ ‹t₂›] = .binOp .or  t₁ t₂ := rfl
      example: [Term| ¬‹t›]        = .unOp  .not t     := rfl

      -- example: [Term| ‹t₁› ∧ ‹t₂› ∧ ‹t₃›]   = .binOp .and (.binOp .and t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› ∧ ‹t₂›) ∧ ‹t₃›] = .binOp .and (.binOp .and t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› ∧ (‹t₂› ∧ ‹t₃›)] = .binOp .and t₁ (.binOp .and t₂ t₃) := rfl
      -- example: [Term| ‹t₁› ∨ ‹t₂› ∨ ‹t₃›]   = .binOp .or  (.binOp .or  t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› ∨ ‹t₂›) ∨ ‹t₃›] = .binOp .or  (.binOp .or  t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› ∨ (‹t₂› ∨ ‹t₃›)] = .binOp .or  t₁ (.binOp .or  t₂ t₃) := rfl

      -- example: [Term| ¬‹t₁› ∧ ‹t₂›]   = .binOp .and (.unOp .not t₁) t₂  := rfl
      example: [Term| ‹t₁› ∧ ¬‹t₂›]   = .binOp .and t₁ (.unOp .not t₂)  := rfl
      -- example: [Term| ¬‹t₁› ∨ ‹t₂›]   = .binOp .or  (.unOp .not t₁) t₂  := rfl
      example: [Term| ‹t₁› ∨ ¬‹t₂›]   = .binOp .or  t₁ (.unOp .not t₂)  := rfl
      example: [Term| ¬(‹t₁› ∧ ‹t₂›)] = .unOp  .not (.binOp .and t₁ t₂) := rfl
      example: [Term| ¬(‹t₁› ∨ ‹t₂›)] = .unOp  .not (.binOp .or  t₁ t₂) := rfl

      -- example: [Term| ‹t₁› ∧ ‹t₂› ∨ ‹t₃› ∧ ‹t₄›] = .binOp .or (.binOp .and t₁ t₂) (.binOp .and t₃ t₄) := rfl
    end Logic

    section Arithmetic
      variable {lhs rhs t₁ t₂ t₃ t₄: Term}

      example: [Term| ‹lhs› + ‹rhs›] = .binOp .add lhs rhs := rfl
      example: [Term| ‹lhs› * ‹rhs›] = .binOp .mul lhs rhs := rfl

      -- example: [Term| ‹t₁› + ‹t₂› + ‹t₃›]   = .binOp .add (.binOp .add t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› + ‹t₂›) + ‹t₃›] = .binOp .add (.binOp .add t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› + (‹t₂› + ‹t₃›)] = .binOp .add t₁ (.binOp .add t₂ t₃) := rfl
      -- example: [Term| ‹t₁› * ‹t₂› * ‹t₃›]   = .binOp .mul (.binOp .mul t₁ t₂) t₃ := rfl
      example: [Term| (‹t₁› * ‹t₂›) * ‹t₃›] = .binOp .mul (.binOp .mul t₁ t₂) t₃ := rfl
      example: [Term| ‹t₁› * (‹t₂› * ‹t₃›)] = .binOp .mul t₁ (.binOp .mul t₂ t₃) := rfl

      example: [Term| ‹t₁› + ‹t₂› * ‹t₃›] = .binOp .add t₁ (.binOp .mul t₂ t₃) := rfl
      -- example: [Term| ‹t₁› * ‹t₂› + ‹t₃›] = .binOp .add (.binOp .mul t₁ t₂) t₃ := rfl

      -- example: [Term| ‹t₁› * ‹t₂› + ‹t₃› * ‹t₄›] = .binOp .add (.binOp .mul t₁ t₂) (.binOp .mul t₃ t₄) := rfl
    end Arithmetic

    section Comparison
      variable {lhs rhs: Term}

      example: [Term| ‹lhs› < ‹rhs›] = .binOp .lt  lhs rhs := rfl
      example: [Term| ‹lhs› ≤ ‹rhs›] = .binOp .lte lhs rhs := rfl
      example: [Term| ‹lhs› > ‹rhs›] = .binOp .gt  lhs rhs := rfl
      example: [Term| ‹lhs› ≥ ‹rhs›] = .binOp .gte lhs rhs := rfl
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

  namespace File
/-!
# Files
-/

  end File
end Total.Stlc.Lang.Surface
