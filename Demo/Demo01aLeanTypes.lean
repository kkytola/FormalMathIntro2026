import Mathlib

namespace AaltoFormalMath2026

set_option linter.unusedTactic false



noncomputable section


section first_examples_of_types

#check 37
#check (37 : ℕ)

#check (norm : ℂ → ℝ)

#check ℝ
#check (ℝ : Type)

end first_examples_of_types


section first_examples_of_propositions

-- A rather uninteresting statement.
#check 1 + 2 = 3 -- Prop

-- A (false) statement.
#check 1 + 2 = 37 -- Prop

-- A more interesting statement.
#check ∀ (x : ℝ), ∃ (n : ℕ), n > x -- Prop

-- Yet another statement.
#check ∃ (n : ℕ), ∀ (x : ℝ), n > x -- Prop

/-- A proof (done in Mathlib) of the more interesting statement. -/
theorem archimedean_property : ∀ (x : ℝ), ∃ (n : ℕ), n > x := by
  exact exists_nat_gt
  done

end first_examples_of_propositions


section one_specific_proposition

/-- A very interesting statement. -/
def P := ∀ (a b c : ℕ+), ∀ (n : ℕ), n > 2 → a^n + b^n ≠ c^n

#check P -- Prop

theorem p : P := by
  unfold P
  sorry
  -- There is a truly remarkable way to fill in the above `sorry`,
  -- but the margins of this file are too small to contain it.
  --
  -- See:
  --
  -- Richard Taylor and Andrew Wiles
  -- Annals of Mathematics 141(3): 553–572, 1995.
  --
  -- Andrew Wiles
  -- Annals of Mathematics 141(3): 443–551, 1995.

end one_specific_proposition


section dummy_propositions

-- In the logic section, we will be manipulating propositions with unspecified content.
-- (Later in the course we will use what we have learned there to manipulate propositions
-- with actual content.)

-- So just like a mathematician might give unspecified real numbers names `x`, `y`, etc.,
-- we will work with unspecified propositions named `P`, `Q`, etc.

variable (P Q : Prop)

#check P -- Prop

-- Compare with
variable (x y : ℝ)
variable (n m l k : ℕ)
variable (z : ℂ)

#check z -- ℂ

end dummy_propositions


end

end AaltoFormalMath2026
