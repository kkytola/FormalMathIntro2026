/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import ImperialCollegeExercises.Preludes.PreludeSec02Sheet5

namespace PreludeSec02

theorem tendsTo_const (c : ℝ) : TendsTo (fun n => c) c := by
  intro ε hε
  dsimp only
  use 37
  intro n hn
  ring_nf
  norm_num
  exact hε

theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) :
    TendsTo (fun n ↦ -a n) (-t) := by
  rw [tendsTo_def] at *
  have h : ∀ n, |a n - t| = |-a n - -t| := by
    intro n
    rw [abs_sub_comm]
    congr 1
    ring
  simpa [h] using ha

theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize ha (ε / 2) (by linarith)
  cases' ha with X hX
  obtain ⟨Y, hY⟩ := hb (ε / 2) (by linarith)
  use max X Y
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hY n hn.2
  rw [abs_lt] at *
  constructor <;> linarith

theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  simpa [sub_eq_add_neg] using tendsTo_add ha (tendsTo_neg hb)

end PreludeSec02
