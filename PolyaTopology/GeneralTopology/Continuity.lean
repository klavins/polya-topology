import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PolyaTopology.GeneralTopology.BasicExamples
import PolyaTopology.GeneralTopology.Closure

/-! @section Continuous Functions -/

universe u v w

namespace GeneralTopology

/-!
@concept epsilon_delta
@title Continuity in a Metric Space
@kind definition

Continuity was defined for functions of a real variable long before topology existed: the image is held inside any tolerance we are given by holding the argument inside a tolerance we choose. Only distances are needed to say it, so it reads in any metric space — and it is the definition the abstract one will have to agree with.
-/

/-!
@problem define_continuous_at
@title Continuity at a Point, and Everywhere
@concept epsilon_delta

@preamble
Let `f` carry one metric space to another. We say `f` is *continuous at* `x` when the image can be held as close to `f x` as we please: for every tolerance `ε > 0` there is a `δ > 0` such that every `x'` within `δ` of `x` has `f x'` within `ε` of `f x`.

The order of the quantifiers is the whole content. The tolerance `ε` is given first and `δ` is found in answer to it, so `δ` may depend on `ε` — and, since this is continuity at one point, on `x` too.

`f` is *continuous* when it is continuous at every point.
@description
Define `Metric.ContinuousAt`, taking a metric `M` on `X`, a metric `N` on `Y`, a map `f : X → Y` and a point `x`, and then `Metric.Continuous`, which says `f` is continuous at every point. Write the two distances as `M.dist x x'` and `N.dist (f x) (f x')`. `∀ ε > 0, p ε` abbreviates `∀ ε, ε > 0 → p ε`.
-/

def Metric.ContinuousAt {X : Type u} {Y : Type v} (M : Metric X) (N : Metric Y) (f : X → Y)
    (x : X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x', M.dist x x' < δ → N.dist (f x) (f x') < ε

def Metric.Continuous {X : Type u} {Y : Type v} (M : Metric X) (N : Metric Y) (f : X → Y) : Prop :=
  ∀ x, M.ContinuousAt N f x

/-- @spec -/
example (X Y : Type) (M : Metric X) (N : Metric Y) (f : X → Y) (x : X) :
    (M.ContinuousAt N f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', M.dist x x' < δ → N.dist (f x) (f x') < ε)
      ∧ (M.Continuous N f ↔ ∀ x, M.ContinuousAt N f x) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! @end -/

/-!
@problem continuous_const_id
@title Constants and the Identity
@concept epsilon_delta

@preamble
The two maps every notion of continuity must admit.

A constant map moves nothing, so the distance between two images is the distance from a point to itself, which is zero and under every tolerance. Any `δ` will serve, and `1` is as good as another.

The identity moves nothing either, in a different sense: the distance between two images *is* the distance between the two points. Here `δ` must be chosen, and `ε` is the choice.
@description
Show that a constant map and the identity are continuous. For the first, `M.dist_self` rewrites the distance away and the tolerance is positive by hypothesis; for the second, offering `ε` leaves a goal that is the hypothesis already.
-/

theorem Metric.continuous_const {X : Type u} {Y : Type v} (M : Metric X) (N : Metric Y) (y : Y) :
    M.Continuous N (fun _ => y) := by
  intro x ε hε
  refine ⟨1, one_pos, ?_⟩
  intro x' _
  rw [N.dist_self]
  exact hε

theorem Metric.continuous_id {X : Type u} (M : Metric X) : M.Continuous M id := by
  intro x ε hε
  exact ⟨ε, hε, fun _ h => h⟩

/-! @end -/

/--
@problem line_continuous_affine
@title An Affine Map of the Line
@concept epsilon_delta

@preamble
The first map whose `δ` is not simply `ε`. Take `t ↦ a * t + b` on the line, with `a ≠ 0`.

The two images differ by `a * (x - x')`, so their distance is `|a|` times the distance between the points. To hold that under `ε` it is enough to hold the distance between the points under `ε / |a|`, which is positive because `|a|` is.

The slope is where the `δ` comes from, and a steeper map needs a smaller one. That is the whole of the exercise, and it is the reason the definition lets `δ` depend on `ε`.
@description
Show that `fun t => a * t + b` is continuous on the line when `a ≠ 0`. Offer `ε / |a|`, positive by `div_pos` and `abs_pos`; `show` restates the goal as the absolute value it is, `ring` names the difference, and `abs_mul` splits it. `mul_div_cancel₀` finishes the arithmetic.
-/
theorem line_continuous_affine (a b : ℝ) (ha : a ≠ 0) :
    line.Continuous line (fun t => a * t + b) := by
  intro x ε hε
  have hpos : 0 < |a| := abs_pos.mpr ha
  refine ⟨ε / |a|, div_pos hε hpos, ?_⟩
  intro x' h
  have hx : |x - x'| < ε / |a| := h
  show |(a * x + b) - (a * x' + b)| < ε
  have e : (a * x + b) - (a * x' + b) = a * (x - x') := by ring
  rw [e, abs_mul]
  calc |a| * |x - x'| < |a| * (ε / |a|) := mul_lt_mul_of_pos_left hx hpos
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hpos)

/-!
@concept continuous_maps
@title Continuity Without Distances
@kind definition

A topological space has no distances, so continuity must be said without them. There is exactly one way, and it is the fact the last section's open sets were for: a map is continuous when the preimage of every open set is open. Every statement about maps in the rest of the subject is made in that form.
-/

/-!
@problem define_continuous
@title The Definition of a Continuous Map
@concept continuous_maps

@preamble
The ε-δ condition cannot be written where there are no distances. What can be written is its consequence: whenever a set is open downstream, the points that land in it form an open set upstream.

So a map between topological spaces is *continuous* when the preimage of every open set is open. Note the direction. The condition is on preimages and not on images, and a continuous map may well carry an open set to a set that is not open — that is a fact about images, not a defect of the definition.

We write `f ⁻¹' U` for the preimage `{x | f x ∈ U}`, and `x ∈ f ⁻¹' U` unfolds to `f x ∈ U`.
@description
Define `Topology.Continuous`, taking a topology `T` on `X`, a topology `T'` on `Y` and a map `f : X → Y`: every set `T'` calls open has a preimage `T` calls open.
-/

def Topology.Continuous {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    (f : X → Y) : Prop :=
  ∀ U, T'.IsOpen U → T.IsOpen (f ⁻¹' U)

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (f : X → Y) :
    T.Continuous T' f ↔ ∀ U, T'.IsOpen U → T.IsOpen (f ⁻¹' U) := Iff.rfl

/-! @end -/

/-!
@problem continuous_id_const_top
@title Constants and the Identity Again
@concept continuous_maps

@preamble
The same two maps, now without distances, and the proofs are shorter for it.

The identity takes each set to itself, so a preimage is the set it came from and openness is the hypothesis. A constant map with value `y` has only two possible preimages: everything, when `y` lies in the set, and nothing, when it does not. Both are open in any topology.
@description
Show that the identity and a constant map are continuous. `Set.preimage_id` rewrites the first; for the second, split on `y ∈ U` with `by_cases` and identify the preimage with `Set.eq_univ_of_forall` or `Set.eq_empty_of_forall_notMem`, each taking a proof that ignores the point.
-/

theorem Topology.continuous_id {X : Type u} (T : Topology X) : T.Continuous T id := by
  intro U hU
  rw [Set.preimage_id]
  exact hU

theorem Topology.continuous_const {X : Type u} {Y : Type v} (T : Topology X)
    (T' : Topology Y) (y : Y) : T.Continuous T' (fun _ => y) := by
  intro U _
  by_cases hy : y ∈ U
  · rw [show (fun _ => y) ⁻¹' U = (Set.univ : Set X) from Set.eq_univ_of_forall (fun _ => hy)]
    exact T.univ
  · rw [show (fun _ => y) ⁻¹' U = (∅ : Set X) from Set.eq_empty_of_forall_notMem (fun _ => hy)]
    exact T.empty

/-! @end -/

/--
@problem continuous_comp
@title The Composite of Two Continuous Maps
@concept continuous_maps

@preamble
Continuity composes, and the reason is that preimages compose: taking the preimage along `g ∘ f` is taking it along `g` and then along `f`.

So an open set upstairs is pulled back to an open set by `g`, and that one is pulled back to an open set by `f`. Nothing about topology enters beyond the definition, which is what one wants of a definition — the continuous maps are the ones a composition law can be built on.
@description
Show that `g ∘ f` is continuous when `f` and `g` are. `Set.preimage_comp` is the equation `g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U)`; after it, apply the two hypotheses in turn.
-/
theorem Topology.continuous_comp {X : Type u} {Y : Type v} {Z : Type w} (T : Topology X)
    {T' : Topology Y} {T'' : Topology Z} {f : X → Y} {g : Y → Z}
    (hf : T.Continuous T' f) (hg : T'.Continuous T'' g) : T.Continuous T'' (g ∘ f) := by
  intro U hU
  rw [Set.preimage_comp]
  exact hf _ (hg U hU)

/-!
@concept continuity_bridge
@title The Two Definitions Agree
@kind theorem

Two definitions of continuity are now in hand, one that needs distances and one that does not. They agree wherever both can be read: a map between metric spaces satisfies the ε-δ condition exactly when it is continuous for the topologies the metrics induce. This is what licenses the abstract definition, and it is the theorem this section is built around.
-/

/--
@problem metric_continuous_iff
@title Epsilon-Delta is Openness of Preimages
@concept continuity_bridge

@preamble
Both directions are short, because the balls do the translating in each.

Suppose `f` satisfies the ε-δ condition and `U` is open. A point `x` of `f ⁻¹' U` has `f x` in `U`, so some ball of radius `ε` about `f x` lies in `U`; continuity at `x` returns a `δ`, and the ball of radius `δ` about `x` lands inside that one, hence inside `U`.

Suppose instead that preimages of open sets are open. Given `x` and `ε`, the ball about `f x` of radius `ε` is open, so its preimage is open, and it contains `x`. Openness of the preimage hands back exactly the `δ` that was wanted.
@description
Prove that `M.Continuous N f` exactly when `M.toTopology.Continuous N.toTopology f`. In both directions the hypotheses fit together without rewriting: a membership in a ball is the distance inequality it abbreviates, and the topology a metric induces calls open exactly what the metric does.
-/
theorem Metric.continuous_iff {X : Type u} {Y : Type v} (M : Metric X) (N : Metric Y) (f : X → Y) :
    M.Continuous N f ↔ M.toTopology.Continuous N.toTopology f := by
  constructor
  · intro hf U hU x hx
    obtain ⟨ε, hε, hball⟩ := hU (f x) hx
    obtain ⟨δ, hδ, hδ'⟩ := hf x ε hε
    exact ⟨δ, hδ, fun y hy => hball (hδ' y hy)⟩
  · intro hf x ε hε
    have hopen := hf (N.ball (f x) ε) (N.isOpenSet_ball (f x) ε)
    obtain ⟨δ, hδ, hsub⟩ := hopen x (N.mem_ball_self (f x) ε hε)
    exact ⟨δ, hδ, fun y hy => hsub hy⟩

/--
@problem affine_continuous_topologically
@title The Affine Map, Read Topologically
@concept continuity_bridge

@preamble
What the bridge buys, in one line. The affine map of the line was shown continuous by producing a `δ` for each `ε`; the bridge turns that, with no further work, into the statement that every open set of the line has an open preimage under it.

This is how every metric example enters the topological subject from here on. One proves the ε-δ statement, where the arithmetic lives, and reads off the topological one.
@description
Show that `fun t => a * t + b` is continuous as a map of topological spaces when `a ≠ 0`. Take the left-to-right direction of the bridge and apply it to the problem already proved.
-/
theorem line_continuous_affine_top (a b : ℝ) (ha : a ≠ 0) :
    line.toTopology.Continuous line.toTopology (fun t => a * t + b) :=
  (line.continuous_iff line _).mp (line_continuous_affine a b ha)

/-!
@concept continuity_closed
@title Closed Sets, Closures and Points
@kind theorem

Open and closed carry the same information, so continuity has a closed-set form, and the two are one statement read through a complement. From it comes the sentence that says what continuity means for the closure operation — a continuous map does not tear a set away from the points it approaches — and the pointwise form that neighbourhoods make available.
-/

/--
@problem continuous_iff_closed
@title Preimages of Closed Sets
@concept continuity_closed

@preamble
A map is continuous exactly when the preimage of every closed set is closed. Nothing is added: taking preimages commutes with complementing, `f ⁻¹' Cᶜ = (f ⁻¹' C)ᶜ`, so the two conditions are the same condition written on the two sides.

That equation, `Set.preimage_compl`, is the whole proof. It is worth noticing why it holds where the corresponding statement for images does not: a point is in the preimage of `Cᶜ` when its image avoids `C`, which is precisely when it avoids the preimage of `C`.
@description
Prove that `T.Continuous T' f` exactly when `T.IsClosed (f ⁻¹' C)` for every closed `C`. Both directions restate a closedness as the openness of a complement — `show T.IsOpen _` — and then move the complement across the preimage; `compl_compl` cancels the two that appear on the way back.
-/
theorem Topology.continuous_iff_closed {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    (f : X → Y) : T.Continuous T' f ↔ ∀ C, T'.IsClosed C → T.IsClosed (f ⁻¹' C) := by
  constructor
  · intro hf C hC
    show T.IsOpen _
    rw [← Set.preimage_compl]
    exact hf Cᶜ hC
  · intro hf U hU
    have hc : T'.IsClosed Uᶜ := by
      show T'.IsOpen _
      rwa [compl_compl]
    have h : T.IsOpen (f ⁻¹' Uᶜ)ᶜ := hf Uᶜ hc
    rw [Set.preimage_compl, compl_compl] at h
    exact h

/--
@problem continuous_closure
@title A Continuous Map Respects Closures
@concept continuity_closed

@preamble
If `x` is approached by `S`, then `f x` is approached by the image of `S`. Said with closures: the image of the closure of `S` lies inside the closure of the image of `S`.

The proof is the closure's least property and nothing else. Pushing the image across, what is to be shown is that `S` lies inside the preimage of the closure of its image. That preimage is closed, being the preimage of a closed set, and it contains `S`, since each point of `S` has its image in the image; so it contains the closure of `S`, which is the claim.

Equality can fail, and the containment is the useful direction anyway.
@description
Show that `f '' (T.closure S) ⊆ T'.closure (f '' S)` for continuous `f`. `Set.image_subset_iff` trades the image on the left for a preimage on the right, and then `T.closure_min` asks for exactly the two facts above.
-/
theorem Topology.continuous_closure {X : Type u} {Y : Type v} (T : Topology X) {T' : Topology Y}
    {f : X → Y} (hf : T.Continuous T' f) (S : Set X) :
    f '' (T.closure S) ⊆ T'.closure (f '' S) := by
  rw [Set.image_subset_iff]
  apply T.closure_min
  · exact (T.continuous_iff_closed T' f).mp hf _ (T'.isClosed_closure (f '' S))
  · intro x hx
    exact T'.subset_closure (f '' S) ⟨x, hx, rfl⟩

/-!
@problem define_continuous_at_top
@title Continuity at a Point, Without Distances
@concept continuity_closed

@preamble
The ε-δ definition was local: it spoke of one point at a time. The topological definition is global, and a local form of it is wanted too. Neighbourhoods supply one, since a neighbourhood is what a ball became.

A map is *continuous at* `x` when every neighbourhood of `f x` has a preimage that is a neighbourhood of `x`. Read with balls in a metric space, that is the ε-δ condition at `x` with the quantifiers hidden inside the word "neighbourhood".
@description
Define `Topology.ContinuousAt`, taking topologies `T` on `X` and `T'` on `Y`, a map `f`, and a point `x` of `X`: every neighbourhood `N` of `f x` has `f ⁻¹' N` a neighbourhood of `x`.
-/

def Topology.ContinuousAt {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) (f : X → Y)
    (x : X) : Prop :=
  ∀ N, T'.IsNbhd (f x) N → T.IsNbhd x (f ⁻¹' N)

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (f : X → Y) (x : X) :
    T.ContinuousAt T' f x ↔ ∀ N, T'.IsNbhd (f x) N → T.IsNbhd x (f ⁻¹' N) := Iff.rfl

/-! @end -/

/--
@problem continuous_iff_continuous_at
@title Continuous Means Continuous at Each Point
@concept continuity_closed

@preamble
The two forms agree, as they did for a metric, and by the same equivalence the last section ended on: a set is open exactly when it is a neighbourhood of each of its points.

Forwards, a neighbourhood of `f x` holds an open `U` around `f x`; its preimage is open, contains `x`, and sits inside the preimage of the neighbourhood.

Backwards, take an open `U` and show its preimage is a neighbourhood of each of its own points. For a point `x` there, `U` is a neighbourhood of `f x`, being open and containing it, so the hypothesis at `x` gives what is wanted.
@description
Prove that `T.Continuous T' f` exactly when `T.ContinuousAt T' f x` for every `x`. `T.isOpen_iff_nbhd` turns the goal of the second direction into a statement at each point, and `T'.nbhd_of_isOpen` makes an open set into a neighbourhood of a point of it.
-/
theorem Topology.continuous_iff_continuousAt {X : Type u} {Y : Type v} (T : Topology X)
    (T' : Topology Y) (f : X → Y) : T.Continuous T' f ↔ ∀ x, T.ContinuousAt T' f x := by
  constructor
  · rintro hf x N ⟨U, hU, hxU, hUN⟩
    exact ⟨f ⁻¹' U, hf U hU, hxU, fun y hy => hUN hy⟩
  · intro hf U hU
    rw [T.isOpen_iff_nbhd]
    intro x hx
    exact hf x U (T'.nbhd_of_isOpen hU hx)

/-!
@concept continuity_examples
@title What the Definition Admits
@kind theorem

The definition is tested against the spaces already built. A discrete space admits every map out of it and a codiscrete space every map into it, so neither constrains anything. The two-point space is the opposite: a map into it is nothing more nor less than an open subset of the space it comes from.
-/

/-!
@problem continuous_extremes
@title Out of the Discrete, Into the Codiscrete
@concept continuity_examples

@preamble
The two extreme topologies are extreme about maps as well, in opposite directions.

Out of a discrete space every map is continuous, whatever the target: the preimage is open because everything is. Into a codiscrete space every map is continuous, whatever the source: the only sets to pull back are the empty one and the whole space, and their preimages are the empty one and the whole space.

So neither extreme can tell any two maps apart, which is why both are useless alone and useful as bounds.
@description
Show the two. The first needs no case analysis at all. For the second, `rintro U (rfl | rfl)` splits the disjunction that defines an open set of the codiscrete topology, and `Set.preimage_empty` and `Set.preimage_univ` name the two preimages.
-/

theorem continuous_from_discrete {X : Type u} {Y : Type v} (T' : Topology Y) (f : X → Y) :
    (discrete X).Continuous T' f :=
  fun _ _ => trivial

theorem continuous_to_codiscrete {X : Type u} {Y : Type v} (T : Topology X) (f : X → Y) :
    T.Continuous (codiscrete Y) f := by
  rintro U (rfl | rfl)
  · rw [Set.preimage_empty]
    exact T.empty
  · rw [Set.preimage_univ]
    exact T.univ

/-! @end -/

/--
@problem sierpinski_open_cases
@title The Sierpiński Space Has Three Open Sets
@concept continuity_examples

@preamble
Before the map, the space. A subset of `Bool` is open in the Sierpiński topology when containing `false` forces containing `true`, and only three subsets pass: the empty set, `{true}`, and the whole space.

The argument is two questions. Does the set contain `false`? If so it contains `true` as well, and a subset of `Bool` containing both is everything. If not, does it contain `true`? If so it is `{true}` exactly, and if not it is empty.

A statement about every element of `Bool` is settled by checking the two, which `cases b` does.
@description
Show that an open set of `sierpinski` is `∅`, `{true}`, or `Set.univ`. Split twice with `by_cases`, and build each equality with `Set.eq_univ_of_forall`, `Set.ext` or `Set.eq_empty_of_forall_notMem`; inside each, `cases b` leaves two goals that the hypotheses in hand close.
-/
theorem sierpinski_open_cases {U : Set Bool} (hU : sierpinski.IsOpen U) :
    U = ∅ ∨ U = {true} ∨ U = Set.univ := by
  by_cases hf : false ∈ U
  · exact Or.inr (Or.inr (Set.eq_univ_of_forall (fun b => by cases b; exacts [hf, hU hf])))
  · by_cases ht : true ∈ U
    · exact Or.inr (Or.inl (Set.ext (fun b => by cases b <;> simp [hf, ht])))
    · exact Or.inl (Set.eq_empty_of_forall_notMem (fun b => by cases b <;> assumption))

/--
@problem sierpinski_classifies_opens
@title A Map to the Sierpiński Space is an Open Set
@concept continuity_examples

@preamble
Now the point of that space. A map `f : X → Bool` is continuous into the Sierpiński topology exactly when `f ⁻¹' {true}` is open — and every open subset of `X` arises this way, from the map sending its points to `true` and the rest to `false`.

So continuous maps into this one two-point space *are* the open subsets of a space, and the whole of a topology is recorded by the maps into it. This is the first sight of a pattern that runs through the subject: a construction is pinned down by the maps it admits.

One direction is the definition at `{true}`, which is open. The other is the three cases above.
@description
Prove that `T.Continuous sierpinski f` exactly when `T.IsOpen (f ⁻¹' {true})`. Forwards, apply the hypothesis to `{true}`, whose openness holds because `false ∈ {true}` is absurd — `simp at h` disposes of it. Backwards, `rcases` the three cases and handle each preimage.
-/
theorem sierpinski_continuous_iff {X : Type u} (T : Topology X) (f : X → Bool) :
    T.Continuous sierpinski f ↔ T.IsOpen (f ⁻¹' {true}) := by
  constructor
  · intro hf
    refine hf {true} ?_
    intro h
    simp at h
  · intro h U hU
    rcases sierpinski_open_cases hU with rfl | rfl | rfl
    · rw [Set.preimage_empty]
      exact T.empty
    · exact h
    · rw [Set.preimage_univ]
      exact T.univ

/-!
@problem continuous_subspace
@title A Subspace Sits in its Space Continuously
@concept continuity_examples

@preamble
The subspace topology was defined by declaring a subset of `A` open when an open set of `X` cuts it out. That is exactly what it takes to make the inclusion continuous, and the inclusion's continuity is the reason the definition is the one it is.

`Subtype.val` is the inclusion, sending a point of `A` — a point of `X` with a proof it lies in `A` — back to the point it was. A preimage under it is the trace on `A` of a set of `X`, so the preimage of an open set is open by definition, with nothing to check.

Composing then restricts any continuous map to a subspace of its source.
@description
Show that the inclusion of a subspace is continuous, and that a continuous map composed with it is continuous. The first is an anonymous constructor whose third component is `rfl`; the second is the composition law, applied to the two maps in the right order.
-/

theorem Topology.continuous_subspace_val {X : Type u} (T : Topology X) (A : Set X) :
    (T.subspace A).Continuous T Subtype.val :=
  fun U hU => ⟨U, hU, rfl⟩

theorem Topology.continuous_restrict {X : Type u} {Y : Type v} (T : Topology X) {T' : Topology Y}
    {f : X → Y} (hf : T.Continuous T' f) (A : Set X) :
    (T.subspace A).Continuous T' (f ∘ Subtype.val) :=
  (T.subspace A).continuous_comp (T.continuous_subspace_val A) hf

/-! @end -/

end GeneralTopology
