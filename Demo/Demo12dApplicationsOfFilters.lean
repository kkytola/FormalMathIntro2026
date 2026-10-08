import Mathlib

set_option linter.unusedVariables false

namespace AaltoFormalMath2026

open Filter
open scoped Topology


section limits_in_topology

#check Filter.Tendsto

#check Continuous
#check nhds -- The "neighborhood filter" (we use notation `𝓝` for `nhds` below).

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/- For a continuous function `f : X → Y` and a point `x₀ ∈ X` we have
`lim f(x) = f(x₀)` as `x → x₀`. -/
example (f : X → Y) (f_cont : Continuous f) (x₀ : X) :
    Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact Continuous.tendsto f_cont x₀

/- In fact, this filter limit condition provides a *characterization* of continuity! -/

-- The actual definition of continuity is the usual one we give in topology:
-- continuity of `f` means that the preimages under `f` of all open sets in the codomain
-- are open in the domain of `f`.
example (f : X → Y) :
    Continuous f ↔ (∀ U, IsOpen U → IsOpen (f ⁻¹' U)) := by
  exact continuous_def

-- However, continuity is first of all equivalent to continuity at all points:
example (f : X → Y) :
    Continuous f ↔ ∀ x₀, ContinuousAt f x₀ := by
  exact continuous_iff_continuousAt

-- And being continuous at a point is defined in terms of limits along neighborhood filters.
example (f : X → Y) (x₀ : X) :
    ContinuousAt f x₀ ↔ Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  rfl

-- So continuity is characterized in terms of limits along neighborhood filters.
example (f : X → Y) (x₀ : X) :
    Continuous f ↔ ∀ x₀, Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact continuous_iff_continuousAt

open Real

-- To provide rich examples of limits in topology (including limits of sequences) the `atTop`
-- filter of "tending to +∞" will be used (and `atBot` correspondingly describes tending to -∞).

#check Filter.atTop -- The "at +∞ filter".
#check Filter.atBot -- The "at -∞ filter".

/- `lim x⁻¹ = -∞` as `x → 0` from the left -/
example : Tendsto (fun (x : ℝ) ↦ x⁻¹) (𝓝[<] 0) atBot := by
  exact tendsto_inv_nhdsLT_zero

/- `lim exp(x) = 0` as `x → -∞` -/
example : Tendsto (fun x ↦ exp x) atBot (𝓝 0) := by
  exact tendsto_exp_atBot

/- `lim exp(x⁻¹) = 0` as `x → 0` from the left -/
example : Tendsto (fun x ↦ exp x⁻¹) (𝓝[<] 0) (𝓝 0) := by
  apply Tendsto.comp tendsto_exp_atBot tendsto_inv_nhdsLT_zero

#check Filter.cocompact -- The "at infinity filter" (idea: "escapes any compact sets").

/- `lim exp(-x²) = 0` as `|x| → +∞` -/
example : Tendsto (fun (x : ℝ) ↦ exp (-(x ^ 2))) (cocompact ℝ) (𝓝 0) := by
  apply Tendsto.comp tendsto_exp_atBot
  apply tendsto_neg_atBot_iff.mpr
  suffices Tendsto (fun x ↦ ‖x‖ ^ 2) (cocompact ℝ) atTop by
    convert this using 1; simp
  apply Tendsto.comp (tendsto_pow_atTop two_ne_zero) tendsto_norm_cocompact_atTop

-- et cetera
-- ...

end limits_in_topology


section asymptotics_of_sequences

open Asymptotics Real

#check Asymptotics.IsBigO -- Landau's asymptotic big-O notation
#check Asymptotics.IsLittleO -- Landau's asymptotic little-O notation

/- A large-looking polynomial (`n ↦ 123π * n⁹⁹⁹⁹⁹⁹`) is still small compared to
an exponential (`o(2ⁿ)`). -/
example :
    IsLittleO (atTop (α := ℕ)) (E := ℝ) (F := ℝ)
      (fun n ↦ 123 * Real.pi * n ^ 999999) (fun n ↦ 2 ^ n) := by
  change IsLittleO (atTop (α := ℕ)) (E := ℝ) (F := ℝ)
            (fun n ↦ (123 * Real.pi) • n ^ 999999) (fun n ↦ 2 ^ n)
  rw [isLittleO_const_smul_left (show 123 * Real.pi ≠ 0 by aesop)]
  apply isLittleO_pow_const_const_pow_of_one_lt 999999
  norm_num

#check IsBigO_def

/- A very weak version of Stirling's approximation: `log n! = O(n * log(n))`. -/
example :
    IsBigO (atTop (α := ℕ)) (E := ℝ) (F := ℝ)
      (fun n ↦ log n.factorial) (fun n ↦ n * log n) := by
  apply IsBigO.of_bound 1
  have obs : Set.Ioi 37 ∈ atTop := by exact Ioi_mem_atTop ..
  filter_upwards [obs] with m hm -- the `filter_upwards` tactic is very useful!
  rw [norm_of_nonneg (r := log m.factorial), norm_of_nonneg (r := m * log m)]
  · simp only [one_mul, ← log_pow]
    apply log_le_log (by positivity)
    exact_mod_cast Nat.factorial_le_pow m
  · positivity
  · positivity

end asymptotics_of_sequences


section derivatives

open Asymptotics Complex

#check HasDerivAt

/- A complex-valued function `f` in the complex plane has derivative `f'(z₀) = a` at
a point `z₀ ∈ ℂ` if and only if `z ↦ f(z) - f(z₀)` is approximated by `z ↦ a * (z - z₀)`
with error of order `o(|z - z₀|)`. -/
example (f : ℂ → ℂ) (z₀ : ℂ) (a : ℂ) :
    HasDerivAt f a z₀ ↔
      (IsLittleO (𝓝 z₀) (fun z ↦ f z - f z₀ - (z - z₀) * a) (fun z ↦ ‖z - z₀‖)) := by
  rw [hasDerivAt_iff_isLittleO]
  simp

end derivatives


section higher_order_vanishing_and_big_O

open Asymptotics Real

open MeasureTheory in
/- If a twice continuously differentiable function `f : ℝ → ℝ` vanishes together with its
first derivative at a point `x₀`, then near that point the function is quadratically small. -/
example (f : ℝ → ℝ) (x₀ : ℝ) (f_smooth : ContDiff ℝ 2 f) (hf : f x₀ = 0) (hf' : deriv f x₀ = 0) :
    IsBigO (𝓝 x₀) f (fun x ↦ |x - x₀| ^ 2) := by
  have f_diff : Differentiable ℝ f := f_smooth.differentiable (by norm_num)
  have df_contDiff : ContDiff ℝ 1 (deriv f) := f_smooth.deriv'
  have df_diff : Differentiable ℝ (deriv f) := df_contDiff.differentiable (by norm_num)
  have df_isBigO : deriv f =O[𝓝 x₀] fun x ↦ x - x₀ := by
    simpa [hf'] using (df_diff x₀).hasDerivAt.isBigO_sub
  obtain ⟨c, c_pos, hc⟩ := df_isBigO.exists_pos
  obtain ⟨δ, δ_pos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hc.bound
  apply IsBigO.of_bound c
  filter_upwards [Metric.ball_mem_nhds x₀ δ_pos] with x hx
  have df_le : ∀ y ∈ Metric.closedBall x₀ (dist x x₀), ‖deriv f y‖ ≤ c * ‖x - x₀‖ := by
    intro y hy
    apply (hδ y ..).trans
    · apply mul_le_mul_of_nonneg_left _ c_pos.le
      exact hy.trans (le_of_eq rfl)
    · exact Metric.closedBall_subset_ball hx hy
  have key_mean_value : ‖f x - f x₀‖ ≤ c * ‖x - x₀‖ * ‖x - x₀‖ := by
    apply (convex_closedBall ..).norm_image_sub_le_of_norm_deriv_le _ df_le <;> aesop
  simpa [hf, pow_two, mul_assoc] using key_mean_value

end higher_order_vanishing_and_big_O


section dominated_convergence_theorem

#check MeasureTheory.ae

/- The formal statement of *Lebesgue's dominated convergence theorem* uses filters in multiple ways:
`Filter.Tendsto` as hypothesis (limit of integrands, with `atTop` and `nhds` filters) and conclusion
(limit of integrals, also with `atTop` and `nhds` filters), `Filter.Eventually` for the
`MeasureTheory.ae` filter for the a.e. limit of integrands hypothesis and for the a.e. domination
hypothesis. -/
#check MeasureTheory.tendsto_integral_of_dominated_convergence

end dominated_convergence_theorem


section general_summation

/- General infinite sums (`∑'`), with values in a space with commutative addition (so that finite
sums can be formed) and topology (so that limits of partial sums can be formed), is defined
in terms of the limit of finite partial sums along the `atTop` filter on the finite sets over
which the partial sum is taken!
(Note! In particular no ordering of terms is needed or used. This is a generalization of "absolute
convergence". It is stronger than "conditional convergence" which relies on forming the partial
sums in a specified order of terms.) -/

/- As an example, here is the concrete characterization of general sums of ℂ-valued terms. -/
example {ι : Type} (a : ι → ℂ) (ha : Summable a) (A : ℂ) :
    ∑' i, a i = A
      ↔ Tendsto (fun s ↦ ∑ i ∈ s, a i) (atTop : Filter (Finset ι)) (𝓝 A) := by
  exact ha.hasSum_iff.symm

end general_summation


end AaltoFormalMath2026
