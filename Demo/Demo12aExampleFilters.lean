import Mathlib

namespace AaltoFormalMath2026


open Filter Set

section ae_filter
/-! ### The "almost everywhere" filter (used in measure theory) -/

open MeasureTheory

-- Let μ be a measure on a space X.
variable {X : Type} [MeasurableSpace X] (μ : Measure X)

/-- Let's build the μ-a.e. filter from scratch. -/
def aeFilter : Filter X where
  sets := {s | μ sᶜ = 0} -- `s ⊆ X` is "almost everything" if the measure of its complement is zero.
  univ_sets := by
    sorry
  sets_of_superset := by
    sorry
  inter_sets := by
    sorry

-- What we constructed above is literally the same as Mathlib's `MeasureTheory.ae μ`.
example : aeFilter μ = MeasureTheory.ae μ := by
  rfl

end ae_filter


section neighborhood_filter
/-! ### The "neighborhoods" filter (used in topology) -/

variable {X : Type} [TopologicalSpace X] (x₀ : X)

-- The "neighborhoods filter" at x₀ ∈ X.
#check nhds x₀

open scoped Topology -- This enables nicer notations in topology.
#check 𝓝 x₀ -- Nicer notation for the neighborhoods filter.

-- Characterization of the "neighborhoods filter" at x₀ ∈ X.
example (s : Set X) :
    s ∈ 𝓝 x₀ ↔ ∃ U, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ s := by
  rw [mem_nhds_iff]
  aesop

-- Characterization of the "punctured neighborhoods filter" at x₀ ∈ X.
example (s : Set X) :
    s ∈ 𝓝[≠] x₀ ↔ ∃ U, (IsOpen U) ∧ (x₀ ∈ U) ∧ (U \ {x₀}) ⊆ s := by
  rw [mem_nhdsWithin]
  rfl

end neighborhood_filter



end AaltoFormalMath2026
