module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace AaltoFormalMathProblems2026

section design_additivity_predicate
/-!
# Problem set 1: Design a predicate of additivity for functions `ℝ → ℝ`

The goal of this problem set is for you to:
 * Write down your definition of what it means for a function `f : ℝ → ℝ` to be additive.
   (`IsAdditive`)
   - The mathematical meaning of additivity of `f` is that the equality `f(x+y) = f(x) + f(y)`
     holds for all possible `x` and `y`.
Then you are supposed to prove some properties about your definition --- in some cases using your
predicate as a hypothesis, and in other cases as a conclusion. Specifically, you will be asked to
show that:
 * The constant function zero (`x ↦ 0`) is additive.
   (`isAdditive_zero`)
 * The function `x ↦ -37 * x` is additive.
   (`isAdditive_neg_thirtyseven_mul_self`)
 * The function `x ↦ x + 37` is not additive.
   (`not_isAdditive_self_add_thirtyseven`)
 * The absolute value function `x ↦ |x|` is not additive.
   (`not_isAdditive_abs`)
 * The value of any additive function `f` at zero is zero, i.e., `f(0) = 0`.
   (`apply_zero_eq_of_isAdditive`)
 * If `f` is additive, then `f(42) + f(-5) = f(37)`.
   (`apply_fortytwo_add_apply_neg_five_eq_of_isAdditive`)
 * The value of any additive function `f` at a natural number `n` is given by `f(n) = n * f(1)`.
   (`apply_nat_eq_mul_apply_one_of_isAdditive`)
 * If both `f` and `g` are additive, then their pointwise sum function `f + g` is also additive.
   (`isAdditive_add`)
The file also contains a *challenge*, which is *not a part of the handed-in problem set*.
The challenge is to prove that:
 * There exists an additive function `f : ℝ → ℝ` which is not linear over the reals.
   (`exists_isAdditive_nonlinear`)
The recommendation is to skip the challenge now (unless you are really really tempted and solved
everything else too easily). Instead the point of noting this challenge is to note that if your
proposed definition of `IsAdditive` implies that an additive `f` is of the form `f(x) = c * x`
for some real number `c ∈ ℝ`, then you have formalized that predicate *incorrectly*!
-/

/-- **DESIGN EXERCISE:** Define a predicate on functions `f : ℝ → ℝ`, which says *"`f` is additive"*.
The mathematical meaning should be: The equality `f(x+y) = f(x) + f(y)` holds for all `x` and `y`
in the domain of definition of `f` (i.e., for all real numbers `x, y ∈ ℝ`). -/
def IsAdditive (f : ℝ → ℝ) : Prop :=
  sorry -- Replace this `sorry` with *your definition*.

end design_additivity_predicate

section use_additivity_predicate

/-- **EXERCISE 1:**
Show (using your definition of additivity), that the constant function zero is additive. -/
lemma isAdditive_zero :
    IsAdditive (fun _ ↦ 0) := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 2:**
Show (using your definition of additivity), that the function `x ↦ -37 * x` is additive. -/
lemma isAdditive_neg_thirtyseven_mul_self :
    IsAdditive (fun x ↦ -37 * x) := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 3:**
Show (using your definition of additivity), that the function `x ↦ x + 37` is not additive. -/
lemma not_isAdditive_self_add_thirtyseven :
    ¬ IsAdditive (fun x ↦ x + 37) := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 4:**
Show (using your definition of additivity), that the absolute value function is not
additive. -/
lemma not_isAdditive_abs :
    ¬ IsAdditive (fun x ↦ |x|) := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 5:**
Show (using your definition of additivity), that if `f` is additive, then `f(0) = 0`. -/
lemma apply_zero_eq_of_isAdditive
    (f : ℝ → ℝ) (f_additive : IsAdditive f) :
    f 0 = 0 := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 6:**
Show (using your definition of additivity), that if `f` is additive, then
`f(42) + f(-5) = f(37)`. -/
lemma apply_fortytwo_add_apply_neg_five_eq_of_isAdditive
    (f : ℝ → ℝ) (f_additive : IsAdditive f) :
    f 42 + f (-5) = f 37 := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **EXERCISE 7:**
Show (using your definition of additivity), that if `f` is additive then `f(n) = n * f(1)`
for all `n ∈ ℕ`. -/
lemma apply_nat_eq_mul_apply_one_of_isAdditive
    (f : ℝ → ℝ) (f_additive : IsAdditive f) (n : ℕ) :
    f n = n * f 1 := by
  -- Note: the proof uses induction. I have already an induction proof skeleton, and
  -- you should only fill in the proofs of the base case and the induction step.
  induction n with
  | zero => -- Base case.
    sorry -- Replace this `sorry` with *your proof* of the base case.
  | succ n hn => -- Induction step.
    sorry -- Replace this `sorry` with *your proof* of the induction step.

/-- **EXERCISE 8:**
Show (using your definition of additivity), that if `f` and `g` are additive, then also `f + g`
is additive.

Here `f + g` means the pointwise sum of the functions: `(f + g)(x) = f(x) + g(x)`.
You can use the lemma `Pi.add_apply` or, e.g., the tactic `dsimp` or `simp` to
unfold this pointwise sum definition of the values of `f + g`. -/
lemma isAdditive_add
    (f g : ℝ → ℝ) (f_additive : IsAdditive f) (g_additive : IsAdditive g) :
    IsAdditive (f + g) := by
  sorry -- Replace this `sorry` with *your proof*.

end use_additivity_predicate

section challenge

/- **CHALLENGE** _(not a part of what you need to hand in)_:
Show (using your definition of additivity), that there exists an additive function `f : ℝ → ℝ`
which is not linear over the reals.

This part is challenging for two reasons. The first reason is that the mathematical content
requires a little bit of thought: all additive functions are in fact linear over the rationals,
and finding a counterexample that is not linear over the reals requires using the axiom of choice
somewhere. The second reason is that at this point of the course we have not covered enough Lean
(and Mathlib) for you to readily be familiar with the necessary parts of the libraries (and
perhaps not even the necessary Lean syntax) to solve the problem. So even if you want to take the
challenge, you may want to wait until you have seen some more formalization of mathematics.

If, however, you attempt the challenge, then you are allowed to add imports to this file:
replace the imports at the top of the file by:
```
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Rat.Star
public import Mathlib.NumberTheory.Real.Irrational
```
or at least
```
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Basis.VectorSpace
```
Your solutions to the previous parts should, however, still compile with the original imports
of this problem set.

The challenge is the following. Uncomment it and add the imports if you want to attempt it.
```
lemma exists_isAdditive_nonlinear :
    ∃ f, IsAdditive f ∧ ¬ ∃ c, ∀ x, f x = c * x := by
  sorry -- Replace this `sorry` with *your proof*.
```


*SPOILER ALERT! Some hints for the challenge are given below:*

















(the Lean declarations mentioned below will make more sense after we have discussed vector spaces
in week 6):
 * Real numbers form a vector space over the field of rational numbers.
   - `Module ℚ ℝ` is an instance
 * The dimension of the `ℚ`-vector space `ℝ` is infinite.
   - (In fact for the proof it suffices to note that dimension is at least two.
 * Every vector space has a basis. (This is where the axiom of choice is used.)
   - `Module.Free.exists_basis`
 * Given a basis of a vector space, one can construct a linear map out of that
   vector space by specifying the values of the map on the basis vectors.
   - `Module.Basis.constr`
   - (A variant of this argument uses the Hahn-Banach extension theorem
      `exists_extension_norm_eq` instead.)
-/

end challenge

end AaltoFormalMathProblems2026
