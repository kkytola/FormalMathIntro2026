-- Logarithms, trigonometric functions and powers: their derivatives, integrals and limits.
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Tactic

namespace AaltoFormalMathProblems2026

/-
# Problem set 6: Design a definition of improper integrals from `0` to `+∞`.

Recall the notion of *improper integrals*, specifically for integrals of functions `f` on the
nonnegative real axis `[0,+∞)`, integrated "from 0 to +∞". The mathematical meaning of the
improper integral is that the integrals of `f` on `(0,r]` (i.e., integrated from `0` to `r`)
exist for all `r ≥ 0`, and their limit as `r → +∞` exists and defines the improper integral.

Note also that this notion of improper integrals is (in some ways) more relaxed than the
measure-theoretic integration of functions `f` on `[0,+∞)`: the latter is meaningful only
when `f` is integrable (so a finite integral of `|f|` exists, too; indeed the difference
between the measure-theoretic integral and improper integral is very analogous to the
difference between absolute summability and existence of limits of partial sums). A typical
example of a function which has an improper integral from `0` to `+∞` but is not integrable
is `x ↦ (sin x) / x`; the improper integral `∫ (sin x) / x dx = π / 2` is important in Fourier
theory, for example. This problem set's non-integrable example function is more complicated
looking, `x ↦ sin x / (log (2 + x)) + cos x / ((2 + x) * (log (2 + x)) ^ 2)`, but actually
easier to handle, since it has an explicit primitive `x ↦ -cos x / log (2 + x)`.

The goal of this problem set is for you to:
 * Write down a definition of what it means for a real-valued function `f` on `[0,+∞)`
   to have an improper integral value `v ∈ ℝ` (integrated from `0` to `+∞`).
   (`HasImproperIntegral`)
   - The mathematical meaning is as explained above.

Then you are supposed to prove some properties about your definition --- in some cases using your
predicate as a hypothesis, and in other cases as a conclusion. Specifically, you will be asked to
show that:
 * The value of the improper integral of `f` is uniquely determined if it exists.
   (`hasImproperIntegral_unique`)
 * If `f₁` has an improper integral with value `v₁` and `f₂` has an improper integral with
   value `v₂`, then `f₁ + f₂` has an improper integral with value `v₁ + v₂`.
   (`hasImproperIntegral_add`)
 * The improper integral of `x ↦ e⁻ˣ` from `0` to `+∞` has the value `1`.
   (`hasImproperIntegral_exp_neg`)
 * The constant function `x ↦ 1` does not have an improper integral (no finite value works).
   (`not_exists_hasImproperIntegral_const_one`)
 * The function `x ↦ (1 + x)⁻¹` does not have an improper integral (no finite value works).
   (`not_exists_hasImproperIntegral_inv_one_add`)
 * The non-integrable function `x ↦ sin x / (log (2 + x)) + cos x / ((2 + x) * (log (2 + x)) ^ 2)`
   has an improper integral with value `(log 2)⁻¹`.
   (`hasImproperIntegral_explicit_nonintegrable`)
-/

open MeasureTheory Topology Real Filter

section improper_integral

/-- **DESIGN EXERCISE:** Give a formal Lean definition of what it means for a function `f : ℝ → ℝ`
to have an improper integral from `0` to `+∞` equal to `v ∈ ℝ`.
The mathematical meaning should be: The function `f` is integrable from `0` to `r`, for
any `r ≥ 0`, and the limit of its integrals from `0` to `r` as `r → +∞` is equal to `v`.
Note also that the function `f` is defined on `ℝ`, but only its values on the nonnegative real axis
should affect the improper integral from `0` to `+∞`. -
-/
def HasImproperIntegral (f : ℝ → ℝ) (v : ℝ) : Prop :=
  sorry -- Replace this `sorry` with *your definition*.

/-- **EXERCISE 1:**
Show (using your definition of improper integrals), that the value of the improper integral of `f`
is uniquely determined, provided it exists. -/
lemma hasImproperIntegral_unique {f : ℝ → ℝ} {v₁ v₂ : ℝ}
    (hfv₁ : HasImproperIntegral f v₁) (hfv₂ : HasImproperIntegral f v₂) :
    v₁ = v₂ := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 2:**
Show (using your definition of improper integrals), that if `f₁` has an improper integral with
value `v₁` and `f₂` has an improper integral with value `v₂`, then `f₁ + f₂` has an improper
integral with value `v₁ + v₂`. -/
lemma hasImproperIntegral_add {f₁ f₂ : ℝ → ℝ} {v₁ v₂ : ℝ}
    (hf₁ : HasImproperIntegral f₁ v₁) (hf₂ : HasImproperIntegral f₂ v₂) :
    HasImproperIntegral (f₁ + f₂) (v₁ + v₂) := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 3:**
Show (using your definition of improper integrals), that the improper integral of `x ↦ e⁻ˣ`
from `0` to `+∞` has the value `1`. -/
lemma hasImproperIntegral_exp_neg :
    HasImproperIntegral (fun x ↦ exp (-x)) 1 := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 4:**
Show (using your definition of improper integrals), that the constant function `x ↦ 1`
does not have an improper integral. (No finite value `v ∈ ℝ` is its improper integral.) -/
lemma not_exists_hasImproperIntegral_const_one :
    ¬ ∃ v, HasImproperIntegral (fun _ ↦ 1) v := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 5:**
Show (using your definition of improper integrals), that the function `x ↦ (1 + x)⁻¹`
does not have an improper integral. (No finite value `v ∈ ℝ` is its improper integral.) -/
lemma not_exists_hasImproperIntegral_inv_one_add :
    ¬ ∃ v, HasImproperIntegral (fun x ↦ ((1 : ℝ) + x)⁻¹) v := by
  sorry -- Replace this `sorry` with *your proof*.

/-
Before the next exercise, I give you some auxiliary results about the function
`x ↦ sin x / (log (2 + x)) + cos x / ((2 + x) * (log (2 + x)) ^ 2)`, which you are
free to use, so that you can focus on the part that relates more directly to your
design choice of `HasImproperIntegral`.
-/

/-- The function `x ↦ (sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2)` is
continuous on the nonnegative real axis. -/
lemma aux_continuousOn :
    ContinuousOn
      (fun x ↦ (sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2))
      (Set.Ici 0) := by
  have aux_ne_zero₁ {x : ℝ} (x_nn : 0 ≤ x) : 2 + x ≠ 0 := by linarith
  have aux_ne_zero₂ {x : ℝ} (x_nn : 0 ≤ x) : log (2 + x) ≠ 0 := (log_pos (by linarith)).ne'
  fun_prop (disch := intro x hx; simp [aux_ne_zero₁ hx, aux_ne_zero₂ hx])

/-- The derivative of the function `t ↦ -cos t / log (2 + t)` at `x ≥ 0` is
`(sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2)`. -/
lemma aux_derivative (x : ℝ) (hx : 0 ≤ x) :
    deriv (fun t ↦ -cos t / log (2 + t)) x =
      (sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2) := by
  have aux_ne_zero₁ : 2 + x ≠ 0 := by linarith
  have aux_ne_zero₂ : log (2 + x) ≠ 0 := (log_pos (by linarith)).ne'
  have h_log : HasDerivAt (fun t ↦ log (2 + t)) (1 / (2 + x)) x := by
    simpa using ((hasDerivAt_id x).const_add 2).log aux_ne_zero₁
  rw [((hasDerivAt_cos x).fun_neg.fun_div h_log aux_ne_zero₂).deriv]
  field_simp
  ring

/-- The integral of function `x ↦ (sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2)`
from `0` to `r ≥ 0` equals `(log 2)⁻¹ - cos r / log (2 + r)`. -/
lemma aux_integral (r : ℝ) (hr : 0 ≤ r) :
    ∫ x in 0..r, (sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2)
      = (log 2)⁻¹ - cos r / log (2 + r) := by
  have aux_ne_zero₁ {x : ℝ} (x_nn : 0 ≤ x) : 2 + x ≠ 0 := by linarith
  have aux_ne_zero₂ {x : ℝ} (x_nn : 0 ≤ x) : log (2 + x) ≠ 0 := (log_pos (by linarith)).ne'
  have obs_subset : Set.uIcc 0 r ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hr]
    exact Set.Icc_subset_Ici_self
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ -cos t / log (2 + t))]
  · simp [neg_div]
    ring
  · intro x hx
    have x_nn : 0 ≤ x := obs_subset hx
    rw [← aux_derivative x x_nn]
    apply DifferentiableAt.hasDerivAt
    fun_prop (disch := simp [aux_ne_zero₁ x_nn, aux_ne_zero₂ x_nn])
  · exact (aux_continuousOn.mono obs_subset).intervalIntegrable

/-- The limit of `cos r / log (2 + r)` as `r → +∞` is `0`. -/
lemma aux_limit :
    Tendsto (fun r ↦ cos r / log (2 + r)) atTop (𝓝 0) := by
  have lim_log : Tendsto (fun r ↦ log (2 + r)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id)
  have cos_bdd : IsBoundedUnder (· ≤ ·) atTop (fun r ↦ |cos r|) :=
    isBoundedUnder_of ⟨1, fun r ↦ abs_cos_le_one r⟩
  simpa [div_eq_mul_inv] using isBoundedUnder_le_mul_tendsto_zero cos_bdd lim_log.inv_tendsto_atTop

/-- **EXERCISE 6:**
Show (using your definition of improper integrals), that the function
`x ↦ (sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2)`
has `(log 2)⁻¹` as the value of its improper integral from `0` to `+∞`. -/
lemma hasImproperIntegral_explicit_nonintegrable :
    HasImproperIntegral
      (fun x ↦ (sin x) / (log (2 + x)) + (cos x) / ((2 + x) * (log (2 + x)) ^ 2))
      (log 2)⁻¹ := by
  sorry -- Replace this `sorry` with *your proof*.

end improper_integral

end AaltoFormalMathProblems2026
