import Mathlib.Tactic

namespace AaltoFormalMathProblems2026


noncomputable section left_continuous_inverse
/-!
# The left-continuous pseudoinverse of the left-continuous pseudoinverse

The goal of this problem set is to build some basic API for a particular situation
which arises for example in probability theory with cumulative distribution functions.
We will abstract the situation a little to (i) improve generality and (ii) simplify
some aspects of the problem.

So instead of a cumulative distribution function `F : ℝ → [0,1]`, we will be talking
about a function `F : R → S` between two complete linear ordered sets (well, types) `R`
and `S`. In a complete linear order `R` (or more generally in a complete lattice) any
set `A : Set R` has a supremum (a least upper bound) `sSup A` and an infimum (a greatest
lower bound) `sInf A`.

In fact `ℝ` is not a *complete* linear order, it is only *conditionally complete*:
the empty set and unbounded sets fail to have supremums and infimums in `ℝ`. So in this
way we are making a stronger hypothesis in order to simplify the problem. The extended real
line `[-∞,+∞] = ℝ ∪ {-∞} ∪ {+∞}` or the unit interval `[0,1]` are actual valid examples
of complete linear orders.

Lean knows that `ℝ` is a conditionally complete linear order:
 * `Real.instConditionallyCompleteLinearOrder : ConditionallyCompleteLinearOrder ℝ`.
Lean also knows that `[-∞,+∞]` is a complete linear order:
 * `instCompleteLinearOrderEReal : CompleteLinearOrder EReal`.
But note that `CompleteLinearOrder ℝ` is simply not true.
(In particular, you will not find such a false statement in Lean or Mathlib.)

Towards the end we will moreover need to assume also that `S` is densely ordered,
i.e., that between any two different elements `y₁ < y₂` in `S` there exists another
one, `y` such that `y₁ < y < y₂`. This assumption is valid in `ℝ`, `[-∞,+∞]`, `[0,1]`
etc., see, e.g.
 * `LinearOrderedSemiField.toDenselyOrdered : DenselyOrdered ℝ`
 * `instDenselyOrderedEReal : DenselyOrdered EReal`.

In this case, we will define a "kind of an inverse function to `F : R → S`",
    `G : S → R` given by
    `G(y) = inf {x ∈ R | F(x) ≥ y}`.
Let us call this the *left-continuous pseudoinverse* of `F`. Or in fact, since that is
a mouthful, let us call that just `G := lcInv F` (we will give `def lcInv := ...` below).
See if you can grasp the intuition of why this `G` is kind of like an inverse to `F`.
Think first, for example, about `F : [0,1] → [0,1]` which is increasing and bijective (and
then moreover continuous). Then think about what if the surjectivity assumption is removed:
then there is a bit of ambiguity in assigning some values of `G` and the choice we make is
the "smallest one which does not break monotonicity". If the injectivity assumption is
removed, then among the many preimages for some values we can only choose one, and the
choice we make is "the smallest preimage".

The main goal will be to prove:
   `inf {y ∈ S | G(y) ≥ x} = sup {F(x') | x' < x}`.
Note that:
 * The left hand side is *by definition* the left-continuous pseudoinverse of the
   left-continuous pseudoinverse of `F`.
 * If `F` is increasing, then the right-hand side `sup {F(x') | x' < x}` is essentially `F(x)`
   itself, except it is modified to become continuous from the left.
So this statement is a variant of the fact that the inverse function of the inverse function
is the original function.

(In principle, proving this could be a slightly tricky exercise in some probability course. If
you want a math challenge, you can figure out the proof for yourself! I have, however, broken
the proof into a number of easier steps for you --- so you can focus on teaching the proof to Lean.)

There are a number of steps before we get to the main goal above. Each step requires quite careful
thinking and careful book-keeping. Lean helps with the book-keeping. The thinking part is
mostly left to you, although I have given hints for most of the steps below.
-/

open Set

-- Lean versions of some of the main assumptions above:
#check CompleteLinearOrder
#check DenselyOrdered

-- Some API of infimums and supremums that you might need:
#check sInf_le        -- The infimum is a lower bound.
#check le_sInf        -- The infimum is greater than any other lower bound.
#check sInf_le_sInf   -- The infimum of a larger set is smaller.
-- You should be able to find (name-guess) similar results about the supremum.

-- And some other useful basic lemmas.
#check lt_of_le_of_lt
#check lt_of_lt_of_le

-- There will probably be other results that you need to find. That is a part of formalization.


-- ## The setup.

-- So now let `R` and `S` be complete linear ordered sets (well, types in Lean).
variable {R : Type} [CompleteLinearOrder R]
variable {S : Type} [CompleteLinearOrder S]

/-- The left-continuous pseudoinverse of a function. -/
def lcInv (F : R → S) (y : S) := sInf {x | y ≤ F x}

variable {F : R → S}

#check lcInv F -- `lcInv F : S → R`

-- **EXERCISE 1:** Prove that...
/-- The function `lcInv F` is increasing. -/
lemma lcInv_mono (F : R → S) :
    Monotone (lcInv F) := by
  -- Quite straightforward, but make sure you know the maths proof first.
  sorry

-- **EXERCISE 2:** Prove that...
lemma lcInv_apply_self_le (x : R) :
    (lcInv F) (F x) ≤ x := by
  -- Very easy, but again make sure you know the maths proof first.
  sorry

-- **EXERCISE 3:** Prove that...
lemma le_sInf_setOf_lcInv_ge (x x' : R) (hx : x' < x) :
    F x' ≤ sInf {y | x ≤ lcInv F y} := by
  -- Hint: First prove that when `x' < x` we have `(lcInv F) (F x') ≤ x' < x`.
  -- Hint: Use a proof by contradiction, where the contradiction is with the property that the
  -- infimum (in the statement) is the greatest lower bound for a set.
  sorry

-- **EXERCISE 4:** Prove that...
lemma sInf_setOf_lcInv_ge_ge_sSup (x : R) :
    sInf {y | x ≤ lcInv F y} ≥ sSup (F '' Iio x) := by
  -- Hint: The key to the maths proof is the previous lemma, `le_sInf_setOf_lcInv_ge`.
  -- First sort out the math details, then this is straightforward.
  sorry

-- **EXERCISE 5:** Prove that...
lemma lcInv_ge_of_sSup_lt (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    lcInv F z ≥ x := by
  -- Hint: The key to that is that for all `x' < x` we have `F x' < z`.
  -- Hint: Use a proof by contradiction, where the contradiction is with the property that the
  -- infimum (in the definition of `lcInv F`) is the greatest lower bound for a set.
  sorry

-- **EXERCISE 6:** Prove that...
lemma ge_sInf_setOf_lcInv_ge (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    z ≥ sInf {y | x ≤ lcInv F y} := by
  -- Hint: This follows straightforwardly from `lcInv_ge_of_sSup_lt`.
  sorry


-- From this point on, we will need the assumption of dense ordering. A key lemma about it
-- is `exists_between`:
#check exists_between

-- A key lemma in the following is `sInf_eq_of_forall_ge_of_forall_gt_exists_lt`:
#check sInf_eq_of_forall_ge_of_forall_gt_exists_lt

-- (A warm-up: an easier version of the key idea. It is also the shortest route to
--  `sInf_setOf_lcInv_ge_le_sSup` two exercises below, so it is worth doing first.)
-- **EXERCISE 7:** As a warm-up for the next one, prove that...
lemma sInf_Ioi {α : Type*} [CompleteLattice α] [DenselyOrdered α] {a : α} :
    sInf (Ioi a) = a := by
  -- Hint: Figure out what `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` is saying
  -- and use it and `exists_between` appropriately.
  sorry

-- **EXERCISE 8:** Prove that...
lemma sInf_setOf_lcInv_ge_le_sSup [DenselyOrdered S] (x : R) :
    sInf {y | x ≤ lcInv F y} ≤ sSup (F '' Iio x) := by
  -- Hint: Show that `sInf {y | x ≤ lcInv F y} ≤ sInf (Ioi (sSup (F '' Iio x)))`.
  -- Then remember the warm-up above.
  sorry

-- **EXERCISE 9:** Prove that...
/-- If `G : S → R` is the left-continuous pseudoinverse of `F : R → S`, then we have
`inf {y ∈ S | G(y) ≥ x} = sup {F(x') | x' < x}`. -/
theorem sInf_setOf_lcInv_ge_eq_sSup [DenselyOrdered S] (x : R) :
    sInf {y | x ≤ lcInv F y} = sSup (F '' Iio x) := by
  -- Hint: This now follows easily by combining the previous results.
  sorry

end left_continuous_inverse

end AaltoFormalMathProblems2026
