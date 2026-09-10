import Mathlib.Tactic

set_option linter.unusedTactic false



namespace AaltoFormalMath2025


section Solving_equations_etc
/-!
### More examples in the spirit of Section02, sheets 1-2

Remember tactics `use` (handling ∃ by providing a witness) and `intro` (handling ∀),
as well as `norm_num` and `ring`.
-/

/-- This is *"Cardano's cubic"*.

There are of course soft existence arguments for roots of cubics, but here
you can just explicitly find a root and use it as a witness to the existential.

If you don't easily find a solution, feel free to use your favorite numerical
software to come up with an educated guess (which you can then prove), or ask
Google, or ask a friend. -/
theorem root_of_cardano_cubic :
    ∃ (x : ℝ), x ^ 3 = 15 * x + 4 := by
  use 4 -- Here we did not really need a complicated solution formula with cube roots.
  norm_num

/- This is asking you for a nontrivial *"Pythagorean triple"*. -/
theorem exists_pythagorean_triple :
    ∃ (a b c : ℕ), a ≠ 0 ∧ b ≠ 0 ∧ (a^2 + b^2 = c^2) := by
  use 3, 4, 5
  grind
  --use 3
  --use 4
  --use 5
  --refine ⟨?_, ?_, ?_⟩
  --· norm_num
  --· norm_num
  --· norm_num

/-- Let's do one with a `∀` quantified, too. -/
example : -- Not bothering to give a name to this, so `example` rather than `theorem`.
    ∀ (a : ℝ), ∃ x, x^4 = 16 * a^4 := by
  intro a
  use 2 * a
  ring

/-- And one more (a factorization of an expression with a parameter). -/
example :
    ∀ (a : ℝ), ∃ (b : ℝ), ∀ (x : ℝ), x^2 - a^2 = (x - a) * (x - b) := by
  -- Maybe you can do this for extra practice.
  sorry

end Solving_equations_etc


end AaltoFormalMath2025
