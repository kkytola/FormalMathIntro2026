import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.FunLike.Fintype
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

namespace AaltoFormalMathProblems2026

/-
# Problem set 3: Design a predicate for symmetries of a square.

The goal of this problem set is for you to:
 * Write down your definition of what it means for a function `f` on the vertices of a square to be a
   symmetry of the square (`IsSquareSymmetry`)
   - The type `Square` will be defined with the four vertices `NE, NW, SW, SE`
     (North-East, North-West, South-West, South-East, counterclockwise along the square).
     The adjacency relation `≈`, indicating whether two different vertices lie on a common side of
     the square, will be such that `NE ≈ NW` (lying on the North side), `NW ≈ SW` (the West side),
     `SW ≈ SE` (the South side), `SE ≈ NE` (the East side), and symmetrically `NW ≈ NE`, `SW ≈ NW`,
     `SE ≈ SW`, `NE ≈ SE`, and no other adjacencies hold.
   - The mathematical meaning of `f : Square → Square` being a symmetry of the square is that
     `f` is bijective on the vertices and preserves the adjacency of vertices (vertices `p` and `q`
     lie on a common side of the square if and only if their images `f(p)` and `f(q)` do).
Then you are supposed to prove some properties about your definition --- in some cases using your
predicate as a hypothesis, and in other cases as a conclusion. Specifically, you will be asked to
show that:
 * The identity function `id : Square → Square` is a symmetry of the square.
   (`isSquareSymmetry_id`)
 * The 90° counterclockwise rotation `rotate : Square → Square` is a symmetry of the square.
   (`isSquareSymmetry_rotate`)
 * The reflection `mirror : Square → Square` across the x-axis is a symmetry of the square.
   Here you are also asked to write down the definition of the reflection and prove that it
   does what it should.
   (`Square.mirror`, ..., `isSquareSymmetry_mirror`)
 * The permutation `NE ↦ NE`, `NW ↦ SW`, `SW ↦ SE`, `SE ↦ NW` is not a symmetry of the square.
   It is a bijection, but it does not preserve adjacency.
   (`not_isSquareSymmetry_scramble`)
 * The map `NE ↦ NE`, `NW ↦ NW`, `SW ↦ NE`, `SE ↦ SE` is not a symmetry of the square either.
   This one is the other way around: it *does* preserve adjacency, but it is not a bijection.
   (`not_isSquareSymmetry_squash`)
 * If both `f` and `g` are symmetries of the square, then their composition `f ∘ g` is
   also a symmetry of the square.
   (`isSquareSymmetry_comp`)

In the end, you will have proven that symmetries of the square form a monoid.
(You could, in fact, prove that they form a group. But handling inverses with the design decision
of this exercise is not as convenient as it would be with a different design that we encounter
later in the course.)

The exercise will involve a lot of explicit combinatorial considerations, for example whether
certain vertex pairs are adjacent or not. The good way is to make heavy use of the tactics that
do case analyses (particularly `cases` and `fin_cases`) and tactics which automate checks of values
or adjacencies (e.g., `simp`, `decide`, `grind`, `aesop`). The design of the types and predicates
involved had better be such that automation of this kind can be used (this requires, in particular,
some decidability and finiteness type class instances recorded).
-/

section Sign
/-! This auxiliary section defines an auxiliary type `Sign = {plus, minus} = {1,-1}` to be used
for the x/y-coordinate signs of sides of the square. -/

/-- The type of plus/minus signs: `{1,-1}`. -/
inductive Sign where
| plus
| minus
deriving DecidableEq, BEq

/-- `Sign` is a two-element type, in particular a finite type. (This instance enables, e.g.,
`decide` and `fin_cases` tactics for `Sign` and eventually for `Square`.) -/
instance Sign.instFintype : Fintype Sign where
  elems := {Sign.plus, Sign.minus}
  complete s := by cases s <;> decide

instance : One Sign where
  one := Sign.plus

instance Sign.instNeg : Neg Sign where
  neg s := match s with
  | .plus => .minus
  | .minus => .plus

@[simp] lemma Sign.plus_eq_one : Sign.plus = 1 := rfl
@[simp] lemma Sign.minus_eq_neg_one : Sign.minus = -1 := rfl

/-- We have `-(-s) = s` for `(s : Sign)`. (This instance enables such `simp` lemmas.) -/
@[simp] lemma Sign.neg_eq_iff (s₁ s₂ : Sign) :
    -s₁ = -s₂ ↔ s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> aesop

instance : InvolutiveNeg Sign where
  neg_neg s := by cases s <;> aesop

/-- `Sign` forms a two-element group under multiplication. -/
instance Sign.instGroup : Group Sign where
  mul s₁ s₂ := if s₁ = s₂ then 1 else -1
  mul_assoc s₁ s₂ s₃ := by cases s₁ <;> cases s₂ <;> cases s₃ <;> aesop
  one_mul s := by cases s <;> aesop
  mul_one s := by cases s <;> aesop
  inv s := s
  inv_mul_cancel s := by cases s <;> aesop

/-- A manual case analysis lemma: `(s : Sign)` is either `1` or `-1`.
Often more automated case analysis by tactics is preferable, however. -/
lemma Sign.eq_plus_or_minus (s : Sign) :
    s = 1 ∨ s = -1 := by
  cases s <;> decide

end Sign

section symmetries_of_the_square

/-- The "square" with four vertices:
`NE = ⟨1,1⟩`, `NW = ⟨-1,1⟩`, `SW = ⟨-1,-1⟩`, `SE = ⟨1,-1⟩`.
The implementation is as a product type `Square := Sign × Sign`. -/
abbrev Square := Sign × Sign

/-- `Square` is a four-element type, in particular a finite type.
(This enables the use of some tactics, e.g., `decide` and `fin_cases`.) -/
instance : Fintype Square := inferInstanceAs (Fintype (Sign × Sign))

/-- `NE = ⟨ 1, 1⟩` as a vertex of `Square` -/
def Square.NE : Square := ⟨ 1,  1⟩

/-- `NW = ⟨-1, 1⟩` as a vertex of `Square` -/
def Square.NW : Square := ⟨-1,  1⟩

/-- `SW = ⟨-1,-1⟩` as a vertex of `Square` -/
def Square.SW : Square := ⟨-1, -1⟩

/-- `SE = ⟨ 1,-1⟩` as a vertex of `Square` -/
def Square.SE : Square := ⟨ 1, -1⟩

/-- Two vertices `p` and `q` of `Square` are equal if their x-coordinates and their y-coordinates
both agree. -/
@[ext] lemma Square.ext {p q : Square} (h1 : p.1 = q.1) (h2 : p.2 = q.2) :
    p = q :=
  Prod.ext h1 h2

/-- A manual case analysis lemma for `(p : Square)`.
Often more automated case analysis by tactics is preferable, however. -/
lemma Square.eq_ne_or_nw_or_sw_or_se (p : Square) :
    p = NE ∨ p = NW ∨ p = SW ∨ p = SE := by
  change ⟨p.1, p.2⟩ = NE ∨ ⟨p.1, p.2⟩ = NW ∨ ⟨p.1, p.2⟩ = SW ∨ ⟨p.1, p.2⟩ = SE
  cases p.1 <;> cases p.2 <;> aesop

/-- The adjacency relation between vertices of `Square`, recorded as an instance of the
`SimpleGraph` type class. We later introduce the notation `≈` for the adjacency relation and
improve its computability/decidability properties. -/
def Square.graph : SimpleGraph Square where
  Adj p q := xor (p.1 = q.1) (p.2 = q.2)
  symm := ⟨fun p q ↦ by grind⟩
  loopless := ⟨fun p ↦ by grind⟩

instance (p q : Square) : Decidable (Square.graph.Adj p q) := by
  change Decidable (xor (p.1 = q.1) (p.2 = q.2))
  infer_instance

/-- Adjacency relation for the vertices of `Square`. -/
notation p " ≈ " q => Square.graph.Adj p q

lemma Square.adj_iff' (p q : Square) :
    (p ≈ q) ↔ xor (p.1 = q.1) (p.2 = q.2) := by
  rfl

/-- An explicit characterization of the adjacency relation of the vertices of the square:
two vertices are adjacent if and only if they either
 * agree on their x-coordinates and disagree on their y-coordinates, or
 * disagree on their x-coordinates and agree on their y-coordinates. -/
lemma Square.adj_iff (p q : Square) :
    (p ≈ q) ↔ ((p.1 = q.1) ∧ (p.2 ≠ q.2)) ∨ ((p.1 ≠ q.1) ∧ (p.2 = q.2)) := by
  grind [Square.adj_iff']

/- *Remark*: Now the adjacency relation should in most cases be handled by `simp [Square.adj_iff]`
and `decide`. E.g.:

```
open Square in
example : NE ≈ NW := by simp [Square.adj_iff]; decide

open Square in
example : ¬ NE ≈ SW := by simp [Square.adj_iff]; decide
```
-/

/-- **DESIGN EXERCISE A:** Define a predicate on functions `f : Square → Square`, which says
_"`f` is a symmetry of the square"_. The mathematical meaning should be:
 1. `f` is bijective;
 2. `f` preserves vertex adjacency (`Square.graph.Adj`) denoted by `≈`
    in the sense that `f(p) ≈ f(q)` holds if and only if `p ≈ q` holds.
-/
def IsSquareSymmetry (f : Square → Square) : Prop :=
  sorry -- Replace this `sorry` with *your definition*.

/-- The type of *symmetries of the square*, defined as the subtype of functions
`f : Square → Square` satisfying the predicate `IsSquareSymmetry` *(defined by you!)*. -/
def SquareSymmetry : Type := { f : Square → Square // IsSquareSymmetry f}

/-- Symmetries of the square can be viewed as functions `Square → Square`. -/
instance : FunLike SquareSymmetry Square Square where
  coe f := f.1
  coe_injective := Subtype.val_injective

/-- **EXERCISE 1:**
Show (using your definition of square symmetries), that the identity function of `Square` is
a symmetry of the square. -/
lemma isSquareSymmetry_id :
    IsSquareSymmetry id := by
  sorry -- Replace this `sorry` with *your proof*.

/-- The rotation of `Square` counterclockwise by 90°. -/
def Square.rotate : Square → Square := fun p ↦ ⟨-p.2, p.1⟩

open Square in
/-- **EXERCISE 2:**
Show (using your definition of square symmetries), that the 90° counterclockwise rotation
`Square.rotate` is a symmetry of the square. -/
lemma isSquareSymmetry_rotate :
    IsSquareSymmetry Square.rotate := by
  sorry -- Replace this `sorry` with *your proof*.

/-- **DESIGN EXERCISE B:** Define a function `Square.mirror : Square → Square`, which performs the
reflection of `Square` across the x-axis.
It could be written `NE ↦ SE`, `NW ↦ SW`, `SW ↦ NW`, `SE ↦ NE`, or more concisely in coordinates
(compare with the definition of `Square.rotate` above). -/
def Square.mirror : Square → Square :=
  sorry -- Replace this `sorry` with *your definition*.

/-- **EXERCISE 3:**
Show that your definition of `Square.mirror : Square → Square` does what it is supposed to do.
(If you have designed the definition well, the proofs here should be `rfl`). -/
lemma Square.mirror_NE : NE.mirror = SE := by sorry -- Replace this `sorry` with *your proof*.
lemma Square.mirror_NW : NW.mirror = SW := by sorry -- Replace this `sorry` with *your proof*.
lemma Square.mirror_SW : SW.mirror = NW := by sorry -- Replace this `sorry` with *your proof*.
lemma Square.mirror_SE : SE.mirror = NE := by sorry -- Replace this `sorry` with *your proof*.

open Square in
/-- **EXERCISE 4:**
Show (using your definition of square symmetries and your definition of the reflection),
that the reflection `Square.mirror` across the x-axis is a symmetry of the square. -/
lemma isSquareSymmetry_mirror :
    IsSquareSymmetry Square.mirror := by
  sorry -- Replace this `sorry` with *your proof*.

/-- A scrambling permutation of the vertices of the `Square`,
defined by `NE ↦ NE`, `NW ↦ SW`, `SW ↦ SE`, `SE ↦ NW`. -/
def Square.scramble : Square → Square
  | ⟨ 1,  1⟩ => NE -- NE ↦ NE
  | ⟨-1,  1⟩ => SW -- NW ↦ SW
  | ⟨-1, -1⟩ => SE -- SW ↦ SE
  | ⟨ 1, -1⟩ => NW -- SE ↦ NW

open Square in
/-- **EXERCISE 5:**
Show (using your definition of square symmetries), that the scrambling permutation
`Square.scramble`: `NE ↦ NE`, `NW ↦ SW`, `SW ↦ SE`, `SE ↦ NW`, is not a symmetry of the square. -/
lemma not_isSquareSymmetry_scramble :
    ¬ IsSquareSymmetry Square.scramble := by
  sorry -- Replace this `sorry` with *your proof*.

/-- A map which collapses two vertices of the `Square`, defined by
`NE ↦ NE`, `NW ↦ NW`, `SW ↦ NE`, `SE ↦ SE`. -/
def Square.squash : Square → Square
  | ⟨ 1,  1⟩ => NE -- NE ↦ NE
  | ⟨-1,  1⟩ => NW -- NW ↦ NW
  | ⟨-1, -1⟩ => NE -- SW ↦ NE
  | ⟨ 1, -1⟩ => SE -- SE ↦ SE

open Square in
/-- **EXERCISE 6:**
Show (using your definition of square symmetries), that the collapsing map `Square.squash`:
`NE ↦ NE`, `NW ↦ NW`, `SW ↦ NE`, `SE ↦ SE`, is not a symmetry of the square. -/
lemma not_isSquareSymmetry_squash :
    ¬ IsSquareSymmetry Square.squash := by
  sorry -- Replace this `sorry` with *your proof*.

open Square in
/-- **EXERCISE 7:**
Show (using your definition of square symmetries), that the composition of two symmetries
of the square is itself a symmetry of the square. -/
lemma isSquareSymmetry_comp {f g : Square → Square}
    (hf : IsSquareSymmetry f) (hg : IsSquareSymmetry g) :
    IsSquareSymmetry (f ∘ g) := by
  sorry -- Replace this `sorry` with *your proof*.

/-- You have basically proven that the symmetries of the square form a monoid.
In fact they form a group, but we will not prove it here. -/
instance SquareSymmetry.instMonoid :
    Monoid SquareSymmetry where
  mul f g := ⟨f ∘ g, isSquareSymmetry_comp f.prop g.prop⟩
  mul_assoc f g h := by rfl
  one := ⟨id, isSquareSymmetry_id⟩
  mul_one f := by rfl
  one_mul f := by rfl

/-
We saw above that the symmetries of the square form a monoid.

In fact they form a group, isomorphic to the dihedral group `D₄`. We don't require you to prove
the group property directly, because for that purpose the design we have adopted above is not the
optimal one (we will later learn about `Equiv`, which is a better starting point for an effective
and convenient design).

Instead, we will next take Mathlib's "abstract" `DihedralGroup 4`, and construct a homomorphism
(which in fact is an isomorphism) from it to `SquareSymmetry`. This turns out to be easy to do,
and using known properties of the dihedral group, we get some relations in `SquareSymmetry` very
easily, which would otherwise require some work to prove.

Abstractly, the dihedral group `Dₙ` is generated by a rotation `r` and a reflection `s`, with
relations `r ^ n = 1`, `s ^ 2 = 1`, and `s * r = r ^ (n-1) * s`.
In Mathlib, `r ^ i` is called `DihedralGroup.r i` and `s` is called `DihedralGroup.sr 0`
(`DihedralGroup.sr i` is the composite `s * r ^ i`, that is, the reflection `s` combined with
a suitable amount of rotation). The relations are `@[simp]`-lemmas in Mathlib, so you probably
don't need their names, but you may look them up. Our case is `n = 4`, and it may be helpful
to examine, e.g.:
```
#check DihedralGroup
#check DihedralGroup 4
#check DihedralGroup.sr (0 : ZMod 4) -- This element will correspond to our `mirror`.
#check DihedralGroup.sr (42 : ZMod 4) -- This element will also correspond to our `mirror`.
#check DihedralGroup.r (1 : ZMod 4) -- This element will correspond to our `rotate`.
#check DihedralGroup.r (37 : ZMod 4) -- This element will also correspond to our `rotate`.
```
-/

/-- The 90° counterclockwise rotation as an element of the monoid (really a group) `SquareSymmetry`. -/
def SquareSymmetry.rotate : SquareSymmetry := ⟨Square.rotate, isSquareSymmetry_rotate⟩

/-- The reflection across the x-axis as an element of the monoid (really a group) `SquareSymmetry`. -/
def SquareSymmetry.mirror : SquareSymmetry := ⟨Square.mirror, isSquareSymmetry_mirror⟩

/-- A monoid homomorphism `DihedralGroup 4 → SquareSymmetry` (which is in fact an isomorphism). -/
def SquareSymmetry.dihedralGroupHom : DihedralGroup 4 →* SquareSymmetry where
  toFun g := match g with
    | .r i => rotate ^ i.val
    | .sr i => mirror * rotate ^ i.val
  map_one' := by rfl
  map_mul' g₁ g₂ := by
    -- *Remark:* If you have designed the definition of `Square.mirror` so that it does
    -- the correct thing and is decidable, then this proof should just be
    -- `fin_cases g₁ <;> fin_cases g₂ <;> decide`. Lean then just checks all 64 cases,
    -- and you don't have to. Replace the sorry by that case-split and decision automation
    -- once you have a good definition of `Square.mirror`.
    sorry -- fin_cases g₁ <;> fin_cases g₂ <;> decide


/-- **EXERCISE 8:**
Prove the commutation relation `mirror * rotate ^ n = rotate ^ (3 * n) * mirror` in
`SquareSymmetry`. -/
lemma SquareSymmetry.mirror_mul_rotate_pow (n : ℕ) :
    mirror * rotate ^ n = rotate ^ (3 * n) * mirror := by
  -- *Hint:*
  -- Recall that in `D₄` we have the relation `s * r = r ^ 3 * s`.
  -- If your first steps are "notice `rotate` is the image of `DihedralGroup.r 1` and
  -- `mirror` is the image of `DihedralGroup.sr 0` under `dihedralGroupHom`",
  -- and your next step is `simp` with the suitably chosen homomorphism properties
  -- of `dihedralGroupHom : DihedralGroup 4 →* SquareSymmetry`, then what remains
  -- should be really easy (since `simp` uses the relations in `DihedralGroup 4`).
  -- (A direct proof of this using only `SquareSymmetry` would be much more work!)
  sorry -- Replace this `sorry` with *your proof*.

end symmetries_of_the_square

end AaltoFormalMathProblems2026
