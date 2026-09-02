module

public import Mathlib.Tactic -- the import the students have practiced under

set_option linter.unusedTactic false

public section

namespace AaltoFormalMathProblems2026

section
/-!
# Problem set 2: Cauchy sequences and bounded sequences on `ℝ`
-/


/-
## Convergent sequences are necessarily Cauchy
-/

-- This is the same definition as in *Section02reals* of the Buzzard & Mehta exercises.
/-- If `n ↦ a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

lemma tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl -- true by definition

/-- If `n ↦ a(n)` is a sequence of reals, `IsCauchy a` is the assertion that
`n ↦ a(n)` is a Cauchy sequence (just as in MS-C1541 Metric Spaces). -/
def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ B, ∀ n m, B ≤ n → B ≤ m → |a n - a m| < ε

lemma isCauchy_def {a : ℕ → ℝ} :
    IsCauchy a ↔ ∀ ε > 0, ∃ B : ℕ, ∀ n m, B ≤ n → B ≤ m → |a n - a m| < ε := by
  rfl -- true by definition

-- EXERCISE 1
/-- Any convergent real-number sequence is necessarily a Cauchy sequence. -/
theorem isCauchy_of_tendsTo {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsCauchy a := by
  -- This is some work --- make sure you know the math proof first!
  -- You may take some inspiration from the uniqueness of limits proof.
  sorry



/-
## Cauchy sequences are necessarily bounded
-/

/-- If `n ↦ a(n)` is a sequence of reals, `IsBounded a` is the assertion that
`n ↦ a(n)` is a bounded sequence (just as in MS-C1541 Metric Spaces). -/
def IsBounded (a : ℕ → ℝ) :=
  ∃ M, ∀ n, |a n| ≤ M

-- EXERCISE 2
-- Before we can prove that all Cauchy-sequences are bounded, we need an auxiliary result.
lemma exists_forall_abs_initial_le (a : ℕ → ℝ) (m : ℕ) :
    ∃ M, ∀ n < m, |a n| ≤ M := by
  -- Induction on `m`; fill in the base case and the induction step.
  induction m with
  | zero => -- Base case.
    sorry
  | succ m ih_m => -- Induction step.
    -- *Hint:* The tactic `omega` can settle the arithmetic about `n < m + 1`.
    sorry

-- EXERCISE 3
/-- Any Cauchy sequence is bounded. -/
theorem isBounded_of_isCauchy {a : ℕ → ℝ} (a_cauchy : IsCauchy a) :
    IsBounded a := by
  -- This is some work --- make sure you know the math proof first!
  sorry

-- EXERCISE 4
-- Now we easily get that:
/-- Any convergent real-number sequence is bounded. -/
theorem isBounded_of_tendsTo {a : ℕ → ℝ} {t : ℝ} (a_lim : TendsTo a t) :
    IsBounded a := by
  -- This is easy now!
  sorry

end

end AaltoFormalMathProblems2026

end
