import Mathlib

namespace AaltoFormalMath2026


open Filter Set

section eventually_and_frequently

-- Let `F` be a filter on a set `X` (well, on a type `X` in Lean).
variable {X : Type} (F : Filter X)
/- As the filter is, by definition, a collection of subsets of `X`, it is helpful to
interpret those subsets contained in the collection as being "large" in some appropriate
sense that is described by the filter. -/

-- Let `P` be a *predicate* on `X`, i.e., a statement `P x` for each `x ∈ X`, which is true or
-- false, depending on `x`.
variable (P : X → Prop)

-- The predicate `P` holds **eventually** along the filter `F` if...
-- ..the subset where the predicate holds is "large".
example : F.Eventually P ↔ {x | P x} ∈ F := by
  rfl

-- The predicate `P` holds **frequently** along the filter `F` if...
-- ...any "large" set has a point where the predicate holds.
example : F.Frequently P ↔ ∀ s ∈ F, ∃ x ∈ s, P x := by
  exact frequently_iff

-- The real-number sequence `(aₙ)` with `aₙ = √n` is eventually larger than an arbitrary fixed
-- constant `c ∈ ℝ` (along the `atTop` filter, i.e., as `n → ∞`).
example (c : ℝ) :
    atTop.Eventually (fun (n : ℕ) ↦ Real.sqrt n > c) := by
  sorry

-- The real-number sequence `(aₙ)` with `aₙ = (-1)ⁿ` is frequently negative (along the `atTop`
-- filter, i.e., as `n → ∞`).
example :
    atTop.Frequently (fun (n : ℕ) ↦ (-1 : ℝ) ^ n < 0) := by
  sorry

end eventually_and_frequently


end AaltoFormalMath2026
