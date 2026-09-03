import Mathlib

namespace AaltoFormalMath2026

open Polynomial
open scoped Polynomial

noncomputable section
-- If we didn't mark things noncomputable, Lean would complain about the definition of `X - 3` etc.

-- Introduce two polynomials `p, q ∈ ℂ[X]` with complex coefficients:
-- `p := X - 3`
-- `q := X + 3`

def p : ℂ[X] := X - 3
def q : ℂ[X] := X + 3

-- Addition of polynomials:
#check p + q

-- Multiplication of polynomials:
#check p * q

-- Some statements about polynomials:
#check p + q = 2 * X
#check p * q = X^2 - 9
--#check p + q = X^361 + 42



section proofs_of_some_statements_about_polynomials
/-!
The first two statements above are true and provable. But Lean does indeed request proofs,
it will not just admit statements. The proofs are not long, given the right tools; we will
learn such tools later, you don't need to worry about the details yet, but you can inspect
what is happening if you want to.
-/

-- The first two statements about are true and provable. But Lean does request proofs.

example : p + q = 2 * X := by
  rw [p, q]
  simp [p, q]
  exact (two_mul X).symm

example : p * q = X^2 - 9 := by
  rw [p, q]
  ring

end proofs_of_some_statements_about_polynomials

end

end AaltoFormalMath2026
