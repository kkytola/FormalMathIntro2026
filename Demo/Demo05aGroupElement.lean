import Mathlib.Tactic


namespace AaltoFormalMath2026


section group_element_triviality
/-!
### Another example in the spirit of Section05, sheet 1
-/

-- Let `G` be a group.
variable (G : Type) [Group G]

-- An element `x ∈ G` which satisfies both `x^5 = 1` and `x^8 = 1`
-- must be the neutral element `1`.
example (x : G) (h5 : x ^ 5 = 1) (h8 : x ^ 8 = 1) : x = 1 := by
  sorry

end group_element_triviality


end AaltoFormalMath2026
