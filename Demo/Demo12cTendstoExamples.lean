import Mathlib

namespace AaltoFormalMath2025


open Filter Set Topology


section order_on_filters

variable {X : Type} (F₁ F₂ : Filter X)

#check F₁ ≤ F₂

-- This is what the order among filters on `X` means be definition:
example : F₁ ≤ F₂ ↔ F₂.sets ⊆ F₁.sets := by
  rfl

/- **Yes!** You read that right: `F₁ ≤ F₂` means `F₁.sets ⊇ F₂.sets`. Although a filter
is, by its definition, a collection of subsets, it should rather be thought of as a
generalized set. Then the collection of subsets consists of those "large" subsets which
contain the generalized set. And the *larger the generalized set* is, the the
*smaller the collection of subsets containing it*! The order relation `≤` on filters
should be thought of as referring to the "size" of the generalized set. -/

end order_on_filters


section pullback_filter

-- Let `f : X → Y` be a function and let `G` be a filter on `Y`.
variable {X Y : Type} (f : X → Y) (G : Filter Y)

#check G.comap f -- Pulling back `G` via `f : X → Y` gives a filter on `X`.

-- This is what the pullback means be definition:
example (s : Set X) :
    s ∈ G.comap f ↔ ∃ u ∈ G, f ⁻¹' u ⊆ s := by
  rfl

/- If one thinks of `G` as a generalized set in `Y`, then the pullback `G.comap f` is a
generalized set in `X` defined essentially as the preimage of the generalized set `G` under `f`.
If one unravels the definition of the filter to the collection of "large subsets", then the
pullback filters large sets are those that are large enough to contain the preimage of some
large set in the original filter. -/

end pullback_filter


section pushforward_filter

-- Let `f : X → Y` a function and let `F` be a filter on `X`.
variable {X Y : Type} (f : X → Y) (F : Filter X)

#check F.map f -- Pushing forward `F` via `f : X → Y` gives a filter on `Y`.

-- This is what the pushforward means:
example (u : Set Y) :
    u ∈ F.map f ↔ ∃ s ∈ F, f '' s ⊆ u := by
  exact mem_map_iff_exists_image

/- If one thinks of `F` as a generalized set in `X`, then the pushforward `F.map f` is a
generalized set in `Y` defined essentially as the image of the generalized set `F` under `f`.
If one unravels the definition of the filter to the collection of "large subsets", then the
pushforward filter's large sets are those which contain the image of some large set in the
original filter. -/

end pushforward_filter


section filter_tendsto

-- Let `f : X → Y` a function and let `F` and `G` be filters on `X` and `Y`, respectively.
variable {X Y : Type} (f : X → Y) (F : Filter X) (G : Filter Y)

/- For intuition about the statement "the function `f` tends to `G` along `F`", it may be
best to think in terms of generalized sets again. -/

#check Filter.Tendsto f F G -- the statement "the function `f` tends to `G` along `F`"
#check F.Tendsto f G -- same, but shorter

-- Here is the definition.
example : F.Tendsto f G ↔ F.map f ≤ G := by
  rfl

-- And here is an equivalent condition.
example : F.Tendsto f G ↔ F ≤ G.comap f := by
  exact tendsto_iff_comap

end filter_tendsto


section some_examples

/- The function `x ↦ eˣ` tends to `0` as `x → -∞`. -/
example : Tendsto Real.exp atBot (𝓝 (0 : ℝ)) := by
  exact Real.tendsto_exp_atBot

/- The function `x ↦ x⁻²` tends to `+∞` as `x → 0` (along the punctured neighborhoods filter). -/
example :
    Tendsto (fun (x : ℝ) ↦ 1 / x^2) (𝓝[≠] (0 : ℝ)) atTop := by
  have aux : -- A good strategy is to compose easier pieces.
      (fun (x : ℝ) ↦ 1 / x^2)
        = (fun (x : ℝ) ↦ x⁻¹) ∘ (fun (x : ℝ) ↦ x ^ 2) := by
    ext x; simp
  rw [aux]
  apply Tendsto.comp -- It suffices to prove the convergence of the pieces, and compose limits!
  · exact tendsto_inv_nhdsGT_zero
  · have obs : Tendsto (fun (x : ℝ) ↦ x ^ 2) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have sq_cont : Continuous (fun (x : ℝ) ↦ x^2) := by continuity
      simpa [ContinuousAt] using sq_cont.continuousAt (x := 0)
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_nhdsWithin_of_tendsto_nhds obs
    · have filt : {0}ᶜ ∈ 𝓝[≠] (0 : ℝ) := by exact self_mem_nhdsWithin
      filter_upwards [filt] with x hx
      simp only [mem_Ioi]
      exact lt_of_le_of_ne (sq_nonneg x) (sq_pos_of_ne_zero hx).ne

end some_examples


end AaltoFormalMath2025
