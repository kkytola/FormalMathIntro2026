import Mathlib.Tactic -- imports all the Lean tactics

set_option linter.unusedTactic false

namespace AaltoFormalMath2026

section
/-!
# Images and preimages of sets under functions
-/

/-
## Images and preimages, recap

Let us quickly recall how to push-forward and pull-back sets in Lean, i.e.,
take images and preimages of sets under a function.
-/

-- Let `f : X → Y` be a function.
variable {X Y : Type} (f : X → Y)

-- The main API for the definitions of images and preimages is
--  * `Set.mem_image`
--  * `Set.mem_preimage`

-- The image of `s : Set X` under `f : X → Y` is by definition...
example (s : Set X) (y : Y) :
    y ∈ f '' s ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image ..

-- The preimage of `t : Set Y` under `f : X → Y` is by definition...
example (t : Set Y) (x : X) :
    x ∈ f ⁻¹' t ↔ f x ∈ t :=
  Set.mem_preimage



/-
## Testing two alternative designs of applying a bijective correspondence to subsets

Imagine that we have two types `X` and `Y`, which are in bijective
correspondence with each other: we have functions `f : X → Y` and
`g : Y → X` such that `g ∘ f = id` (identity map of `X`) and `f ∘ g = id`
(identity map of `Y`), i.e., `f` and `g` are bijections which are the
inverses of each other.
-/

variable {X Y : Type} (f : X → Y) (g : Y → X) (hfg : f ∘ g = id) (hgf : g ∘ f = id)

-- Let us also recall the definition of bijectivity in Lean:
example :
    Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f := by
  rfl -- ...by definition

/-
This situation arises in formalization in particular when `X` and `Y` really
are just copies (type synonyms) of the same type, but we wish to equip them
with different structures.

*Aside*:
One concrete example is the dual to a normed space `V` (over `ℝ`, say) equipped
with either the dual norm topology or with the weak-* topology. Mathlib has
two synonymous types defined, `NormedSpace.Dual ℝ V` and `WeakDual ℝ V`,
both literally consisting of all continuous linear functionals on `V`.
The former comes equipped with the dual norm and the topology induced by it, and
the latter one comes equipped with the weak-* topology; don't worry if you don't
know what these are exactly --- the point is that the "elements" of both types
are the same but some structure we introduce on the types is different for good
reasons. So these two synonymous types are really the same; in this setup both
`f` and `g` would really be essentially the identity function (up to identifying
the synonymous types). And we sometimes need to transport sets from one type to
its synonymous copy by these identity functions.

*...back to the experiment...*

In this situation we should not only be able to identify points `x : X`
with corresponding points `y = f x : Y` via the bijection `f`, but we often
also want to identify subsets `s : Set X` of `X` with subsets of `Y`.
There are two obvious ways to do this:
 * we can map `s : Set X` to its image `f '' s : Set Y` under `f : X → Y`
 * we can map `s : Set X` to its preimage `g ⁻¹' s : Set Y` under `g : Y → X`
and both yield mathematically the same result under the above hypothesis
that `f` and `g` are inverses to each other.
-/

#check fun s ↦ f '' s    -- `Set X → Set Y`
#check fun s ↦ g ⁻¹' s   -- `Set X → Set Y`

/-
Which one is a better choice? In the following, we try out both (and learn the
hard way).

You are allowed to use all lemmas from Mathlib here. You can find them by guessing names
or using `exact?` at a suitable point. An example of a relevant lemma might be
`Set.preimage_union`; you can probably now guess the names of a few similar ones.
-/

-- DEMO 1a
-- Let us first show that `g ⁻¹'` respects unions.
example (s₁ s₂ : Set X) :
    g ⁻¹' (s₁ ∪ s₂) = (g ⁻¹' s₁) ∪ (g ⁻¹' s₂) := by
  sorry

-- DEMO 1b
-- Let us then show that also `f ''` respects unions.
example (s₁ s₂ : Set X) :
    f '' (s₁ ∪ s₂) = (f '' s₁) ∪ (f '' s₂) := by
  sorry

-- DEMO 2a
-- Then let us show that `g ⁻¹'` respects intersections.
example (s₁ s₂ : Set X) :
    g ⁻¹' (s₁ ∩ s₂) = (g ⁻¹' s₁) ∩ (g ⁻¹' s₂) := by
  sorry

-- DEMO 2b
-- And that `f ''` respects intersections.
example (s₁ s₂ : Set X) :
    f '' (s₁ ∩ s₂) = (f '' s₁) ∩ (f '' s₂) := by
  sorry

-- DEMO 3a
-- Same with complements, `g ⁻¹'` respects them.
example (s : Set X) :
    g ⁻¹' sᶜ = (g ⁻¹' s)ᶜ := by
  sorry

-- DEMO 3b
-- And finally, also `f ''` respects complements.
example (s : Set X) :
    f '' sᶜ = (f '' s)ᶜ := by
  sorry

-- Was `f ''` (image/push-forward) or `g ⁻¹'` (preimage/pull-back) easier to deal with?
-- Why was the other one harder?

-- So which one is a better choice for transporting sets between types which
-- are in bijective correspondence?




/-
## Constructing a counterexample

You probably noticed that the reason images are worse than preimages in this situation
is that images do not generally respect set operations such as intersections or
complements; for that one needs extra hypotheses of injectivity or bijectivity, which
can be annoying for the user to provide even if they are true in the situation at hand.
The better design is to use preimages, which respect set operations generally, so the
user does not need to provide the extra hypotheses.

As a final exercise of this sheet, let us construct counterexamples to preservation
of intersections in the absence of the extra assumptions.

Let us `#check Set.image_inter` to find out its precise type signature.

`Set.image_inter {X Y : Type} {f : X → Y} {s₁ s₂ : Set X} (H : Function.Injective f) :`
`  f '' (s₁ ∩ s₂) = (f '' s₁) ∩ (f '' s₂)`

Our goal now is to show that in `Set.image_inter` we cannot drop the injectivity
assumption `H`. Specifically, we will prove the negation:

`¬ (∀ (X Y : Type) (f : X → Y) (s₁ s₂ : Set X), f '' (s₁ ∩ s₂) = (f '' s₁) ∩ (f '' s₂))`

To fill in the `sorry` below that is a placeholder for the proof of this, we need to
construct a counterexample: define two concrete types `X` and `Y`, a function `f : X → Y`,
and two sets `s₁, s₂ ⊆ X` such that `f '' (s₁ ∩ s₂) ≠ f '' s₁ ∩ f '' s₂`.
-/

-- DEMO 4 (showing that the injectivity hypothesis cannot be dropped from `Set.image_inter`).
example :
    ¬ (∀ (X Y : Type) (f : X → Y) (s₁ s₂ : Set X),
        f '' (s₁ ∩ s₂) = (f '' s₁) ∩ (f '' s₂)) := by
  sorry


end

end AaltoFormalMath2026
