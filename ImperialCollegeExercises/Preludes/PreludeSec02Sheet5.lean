/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic

namespace PreludeSec02

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
  Iff.rfl

end PreludeSec02
