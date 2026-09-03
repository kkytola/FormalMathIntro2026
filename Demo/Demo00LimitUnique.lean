import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic

namespace AaltoFormalMath2026

noncomputable section
/-!
# A first look at Lean: uniqueness of limits

This is meant as the first example of how a Lean proof looks like and how to interact with it.
-/

open Metric MetricSpace
-- Enable succinct names and notation for metric space-related notions.

variable {X : Type} [MetricSpace X]  -- Let `X` be a metric space.
variable (x : ℕ → X)                 -- Let `x` be a sequence in `X`.
variable (a b : X)                   -- Let `a` and `b` be points in `X`.

-- Metric space axioms from Mathlib, as a reassurance that they are just like in MS-C1541.
#check dist_triangle  -- dist x z ≤ dist x y + dist y z
#check dist_eq_zero   -- dist x y = 0 ↔ x = y
#check dist_comm      -- dist x y = dist y x

/-- The definition of a limit of a sequence in a metric space `X`
(just like in MS-C1541 Metric Spaces). -/
def HasLimit (x : ℕ → X) (a : X) :=
  ∀ ε > 0, ∃ N, ∀ n, n ≥ N → dist (x n) a < ε

/-- A sequence in a metric space cannot have two different limits
(i.e., any two limits of the sequence must be equal). -/
theorem limit_unique
    (lim_is_a : HasLimit x a) (lim_is_b : HasLimit x b) :
    a = b := by
  suffices dist_le_any_pos : ∀ ε > 0, dist a b ≤ ε by
    apply dist_eq_zero.mp (le_antisymm ?_ dist_nonneg)
    exact le_of_forall_pos_le_add (by grind)
  intro ε ε_pos
  obtain ⟨N₁, key₁⟩ : ∃ N, ∀ n ≥ N, dist (x n) a < ε/2 :=
    lim_is_a (ε/2) (by linarith)
  obtain ⟨N₂, key₂⟩ : ∃ N, ∀ n ≥ N, dist (x n) b < ε/2 :=
    lim_is_b (ε/2) (by linarith)
  let n := max N₁ N₂
  have n_large₁ : n ≥ N₁  := le_max_left N₁ N₂
  have n_large₂ : n ≥ N₂  := le_max_right N₁ N₂
  have near₁ : dist (x n) a < ε/2       := key₁ n n_large₁
  have near₂ : dist (x n) b < ε/2       := key₂ n n_large₂
  calc dist a b
   _ ≤ dist a (x n) + dist (x n) b      := ?_
   _ ≤ ε/2 + ε/2                        := add_le_add ?_ near₂.le
   _ = ε                                := by ring
  · exact dist_triangle a (x n) b
  · simpa [dist_comm] using near₁.le



section additional_note_on_special_cases
/-!
The main purpose was to explore a bit how Lean proofs look like and how to interact
with them. The following is just an extra remark on generality that I think is worth making.

The theorem `limit_unique` was proven assuming `X` is a metric space. It now works out of the
box for whatever specific metric spaces we might care about: for example `ℝ`, `ℂ`, various
function spaces, etc. Two illustrations:
-/

-- Let us first exemplify with `ℂ`.
example (z : ℕ → ℂ) (a b : ℂ) (lim_is_a : HasLimit z a) (lim_is_b : HasLimit z b) :
    a = b := by
  exact limit_unique z _ _ lim_is_a lim_is_b
  -- This worked right out of the box. Lean knew that `ℂ` is a metric space and
  -- was able to apply the general result we proved above for the special case `X = ℂ`.

-- Another example is the space of bounded continuous functions on a topological space Z.

variable (Z : Type) [TopologicalSpace Z]

open BoundedContinuousFunction
#check Z →ᵇ ℝ -- The space of functions Z → ℝ which are bounded and continuous.

example (f : ℕ → (Z →ᵇ ℝ)) (g h : Z →ᵇ ℝ)
    (lim_is_g : HasLimit f g) (lim_is_h : HasLimit f h) :
    g = h := by
  exact limit_unique f _ _ lim_is_g lim_is_h
  -- This also worked right out of the box. Lean knew that the set of bounded continuous
  -- real-valued functions on a topological space `Z` is a metric space (the metric used by
  -- default is induced by the sup-norm) and Lean was again able to apply the general result
  -- we proved above for the special case `X = (Z →ᵇ ℝ)`.

end additional_note_on_special_cases



end -- section

end AaltoFormalMath2026
