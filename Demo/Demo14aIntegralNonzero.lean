import Mathlib

set_option linter.unusedVariables false

namespace AaltoFormalMath2026

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section nonvanishing_integral
/-!
# Nonzero nonnegative continuous functions have nonvanishing integrals

The goal of this demo sheet is to prove that if `f` is a continuous nonnegative function on
a nondegenerate interval `[a,b]` which is not identically zero on the interval, then the
integral of `f` is positive,  `∫ₐᵇ f(x) dx > 0`.

As you probably observed right away, the key lemma is that such a continuous `f` has to be
larger than some positive constant `c > 0` on some small interval around a point `z ∈ (a,b)`
where `f(z) ≠ 0`. And therefore by monotonicity of integrals we get `∫ₐᵇ f(x) dx ≥ c * L > 0`
where `L > 0` is the length of the small interval.

Very easy, right? (An informal text might call the above paragraph a complete proof.)

But as we are about to learn...
    ...it takes some work to provide a complete Lean proof...
    ...and some thinking is required even to formulate a precise Lean statement!

Regarding the statement, note that mathematically there are two kinds of integrals
(in fact many more, but two good measure-theoretic notions of integral that are worth
using; forget about poorly-behaved Riemann integrals etc.!):
 * *Lebesgue integrals* of functions with values in [0,+∞] (i.e., in `ENNReal`)
 * *Bochner integrals* of functions with values in Banach spaces (e.g., in `ℝ`).
In informal math we just denote both by `∫` and we seldom explicitly mention which one
we are using when.

Lebesgue integrals are nice because they always exist (under measurability assumption
of the integrand), but it can get quite annoying to make everything `ENNReal`-valued.

Bochner integrals are annoying, because their existence requires integrability in addition
to measurability of the integrand, but on the other hand, they allow to work directly with
real values of the integrand and of the integral, which is definitely nicer than coercing
back and forth with `ENNReal`.

Either choice is annoying, for different reasons. So let's do both!
-/

-- We will consider an interval `[a,b] ⊆ ℝ` which is nondegenerate, `a < b`.
variable {a b : ℝ} (a_lt_b : a < b)

-- The closed interval `[a,b] ⊆ ℝ` is denoted by
#check Icc a b
-- In the precise reasoning, we will also use the open interval `(a,b) ⊆ ℝ`
#check Ioo a b
-- and the half-open interval `(a,b] ⊆ ℝ` (this is the implicit choice in `intervalIntegral`)
#check Ioc a b

-- We assume that `f` is a continuous real-valued function on `[a,b]`.
-- In fact it is nicer to have `f` defined on all of `ℝ`, and assuming continuity
-- on all of `ℝ` makes life easier and can be done without loss of generality.
variable (f : ℝ → ℝ) (f_cont : Continuous f)

-- And of course we wanted `f` to be nonnegative, and nonzero at some point in the interval.
-- Again to make this slightly easier, let's directly assume (without loss of generality)
-- that `f` is nonzero at some point of the open interval `(a,b)`.
variable (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0)

-- The following is the key lemma --- regardless of which of the two integrals (Lebesgue
-- or Bochner) one chooses to use.
lemma exists_forall_mem_Ioo_gt (a_lt_b : a < b)
    (f_cont : Continuous f) (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0) :
    ∃ c > 0, ∃ a' ∈ Icc a b, ∃ b' ∈ Icc a b,
      (a' < b') ∧ (∀ x ∈ Ioo a' b', c ≤ f x) := by
  sorry

/-
The following is the *Lebesgue integral version of the main statement* of this problem sheet.
I think it is slightly easier of the two, because Lebesgue integrals are better behaved and the
library contains more useful and easier to apply results about the Lebesgue integral. -/
theorem main_goal₁ (a_lt_b : a < b)
    (f_cont : Continuous f) (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0) :
    0 < ∫⁻ x in Ioc a b, ENNReal.ofReal (f x) := by
  -- Mathematically the key is the lemma `exists_forall_mem_Ioo_gt` above and
  -- monotonicity of integrals.
  sorry

/-
The following is the *Bochner integral version of the main statement* of this problem sheet.
The statement looks slightly nicer because we do not need to coerce the function values, but
I think this is in fact slightly trickier, because Bochner integrals and especially their special
case of integrals along intervals of the real line have fewer good general results about them
directly available in the library. -/
theorem main_goal₂ (a_lt_b : a < b)
    (f_cont : Continuous f) (f_nn : 0 ≤ f) (f_ne_zero : ∃ z ∈ Ioo a b, f z ≠ 0) :
    0 < ∫ x in a..b, f x := by
  -- Mathematically the key is again the lemma `exists_forall_mem_Ioo_gt` above
  -- and monotonicity of integrals.
  sorry

end nonvanishing_integral

section the_general_setup_for_lebesgue_and_bochner_integrals

variable (X : Type)
variable [MeasurableSpace X] -- A sigma-algebra of measurable sets on `X`.
variable (μ : Measure X) -- A measure `μ` on the space `X`.

variable (A : Set X) -- A set in X (i.e., what in math would be called a subset A ⊆ X)
#check MeasurableSet A -- The proposition about whether or not `A` is a measurable set.

-- A function `f₁` on `X` with values in extended nonnegative reals, ℝ≥0∞ = [0,+∞]
variable (f₁ : X → ℝ≥0∞)

#check Measurable f₁ -- The proposition about whether `f₁ : X → ℝ≥0∞` is a measurable function.

-- The Lebesgue integral of `f₁ : X → [0,+∞]` and the Lebesgue integral of `f₁` on the set `A ⊆ X`
#check ∫⁻ x, f₁ x ∂μ
#check ∫⁻ x in A, f₁ x ∂μ

-- A real-function `f₂` on `X`
variable (f₂ : X → ℝ)

#check Measurable f₂ -- The proposition about whether `f₂ : X → ℝ` is a measurable function.

-- The Bochner integral of `f₂ : X → ℝ` and the Bochner integral of `f₂` on the set `A ⊆ X`.
#check ∫ x, f₂ x ∂μ
#check ∫ x in A, f₂ x ∂μ

-- A complex-function `f₃` on `X`
variable (f₃ : X → ℂ)

-- The Bochner integral of `f₃ : X → ℂ` and the Bochner integral of `f₃` on the set `A ⊆ X`.
#check ∫ x, f₃ x ∂μ
#check ∫ x in A, f₃ x ∂μ

-- The `intervalIntegral` is just a convenient special case of Bochner integrals with respect to the
-- standard measure `volume` on the real line, over subsets of the form `(a,b] ⊆ ℝ` (intervals).
example (g : ℝ → ℂ) (a b : ℝ) (a_lt_b : a < b) :
    ∫ x in a..b, g x = ∫ x in Ioc a b, g x ∂volume := by
  simp only [intervalIntegral]
  have backwards_nothing : Ioc b a = ∅ := by grind
  simp [backwards_nothing]

end the_general_setup_for_lebesgue_and_bochner_integrals

end AaltoFormalMath2026
