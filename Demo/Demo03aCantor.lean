import Mathlib

namespace AaltoFormalMath2026


noncomputable section cantors_theorem

open Function Set

variable (X : Type)

/-- The cardinality of the power set `Set X` is strictly greater than the cardinality of `X`,
i.e., there does not exist any surjective function `X → Set X`. -/
theorem cantors_theorem :
    ¬ ∃ f : X → Set X, Surjective f := by
  intro maybe
  obtain ⟨f, f_surj⟩ := maybe
  let B : Set X := {x | x ∉ f x}
  specialize f_surj B
  obtain ⟨b, fb_eq_B⟩ := f_surj
  by_cases h : b ∈ B
  · have h' : b ∉ B := by
      simp [B] at h
      rw [fb_eq_B] at h
      exact h
    contradiction
  · have h' : b ∈ B := by
      simp [B] at h
      rw [fb_eq_B] at h
      exact h
    contradiction

end cantors_theorem


end AaltoFormalMath2026
