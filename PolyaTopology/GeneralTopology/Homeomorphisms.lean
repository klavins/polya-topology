import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Continuity

/-! @section Homeomorphisms -/

universe u v w

namespace GeneralTopology

/-!
@concept homeomorphism
@title Homeomorphisms
@kind definition

Two spaces that differ only in the names of their points ought to count as the same space. A continuous map with a continuous inverse says exactly that: it matches the points of one with the points of the other and the open sets of one with the open sets of the other, so nothing a topology can see tells the two apart. This is the subject's notion of sameness.
-/

/-!
@problem define_homeomorphism
@title The Definition of a Homeomorphism
@concept homeomorphism

@preamble
A continuous map carries one space into another, but it may lose almost everything on the way: a constant map is continuous and remembers nothing. A map loses nothing when it can be undone by a map of the same kind.

So a *homeomorphism* is a pair of maps, one each way, each continuous, whose composites in both orders are the identity. Both conditions are stated pointwise: `invFun (toFun x) = x` for every `x` of `X`, and `toFun (invFun y) = y` for every `y` of `Y`.

As with `Metric` and `Norm`, the pair and its four conditions are bundled into a structure carried as an ordinary argument.
@description
Define the structure `Homeomorphism`, on a topology `T` on `X` and a topology `T'` on `Y`, with six fields in this order: `toFun`, `invFun`, then `left_inv` and `right_inv` carrying the two inverse conditions, then `continuous_toFun` and `continuous_invFun` carrying the two continuities. Bind `X` and `Y` implicitly, since the two topologies fix them.
-/

structure Homeomorphism {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) where
  toFun : X → Y
  invFun : Y → X
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
  continuous_toFun : T.Continuous T' toFun
  continuous_invFun : T'.Continuous T invFun

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (h : Homeomorphism T T') :
    (∀ x, h.invFun (h.toFun x) = x) ∧ (∀ y, h.toFun (h.invFun y) = y)
      ∧ T.Continuous T' h.toFun ∧ T'.Continuous T h.invFun := by
  refine ⟨fun x => ?_, fun y => ?_, h.continuous_toFun, h.continuous_invFun⟩
  · apply h.left_inv
  · apply h.right_inv

/-! @end -/

/-!
@problem homeomorphism_bijective
@title The Underlying Map is a Bijection
@concept homeomorphism

@preamble
The definition was stated as four conditions on maps, and nothing was said about the points. It has settled the points all the same: a map with an inverse on both sides is a bijection, and the inverse map is the inverse bijection.

Injectivity comes from the left condition. If two points have the same image, apply the inverse to both sides; each returns to the point it came from, so the points were equal. Surjectivity comes from the right condition, which exhibits a preimage for every point of `Y`.

`Function.Injective f` says that `f x = f x'` forces `x = x'`, and `Function.Surjective f` that every `y` is `f x` for some `x`.
@description
Show that the forward map of a homeomorphism is injective and surjective. For injectivity, rewrite both sides of the goal backwards with `h.left_inv` and the hypothesis closes it; for surjectivity, the point wanted is the image of `y` under the inverse.
-/

theorem Homeomorphism.injective {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphism T T') : Function.Injective h.toFun := by
  intro x x' hx
  rw [← h.left_inv x, ← h.left_inv x', hx]

theorem Homeomorphism.surjective {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphism T T') : Function.Surjective h.toFun :=
  fun y => ⟨h.invFun y, h.right_inv y⟩

/-! @end -/

/-!
@problem homeomorphism_refl_symm
@title The Identity and the Inverse
@concept homeomorphism

@preamble
A space is the same space as itself, by the identity map, which is its own inverse and is continuous in both directions.

And the relation is symmetric, for a reason worth noticing: the definition is already symmetric in its two maps. Exchanging `toFun` with `invFun` exchanges the two inverse conditions with each other and the two continuities with each other, so a homeomorphism from `T` to `T'` becomes one from `T'` to `T` with no work at all.
@description
Define `Homeomorphism.refl T`, the identity homeomorphism from `T` to itself, and `Homeomorphism.symm h`, the homeomorphism the other way. Every field of each is either `rfl`, `Topology.continuous_id` at the topology in hand, or one of the fields of `h` under a different name.
-/

def Homeomorphism.refl {X : Type u} (T : Topology X) : Homeomorphism T T where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := Topology.continuous_id T
  continuous_invFun := Topology.continuous_id T

def Homeomorphism.symm {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphism T T') : Homeomorphism T' T where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (h : Homeomorphism T T')
    (x : X) (y : Y) :
    (Homeomorphism.refl T).toFun x = x ∧ (Homeomorphism.refl T).invFun x = x
      ∧ h.symm.toFun y = h.invFun y ∧ h.symm.invFun x = h.toFun x :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem homeomorphism_trans
@title The Composite of Two Homeomorphisms
@concept homeomorphism

@preamble
Sameness is transitive, and the composite is what shows it. Compose the forward maps in one order and the inverse maps in the other; each composite of the two is the identity because the inner pair cancels first and the outer pair then cancels.

The continuities are the composition law of the last section, applied once in each direction. Three spaces means three types, so the statement carries three universe variables.
@description
Define `Homeomorphism.trans h h'`, the composite homeomorphism from `T` to `T''`. For the two inverse conditions, `show` restates the goal with the composition unfolded and two rewrites cancel the pairs; for the two continuities, `Topology.continuous_comp` takes the topology of the source and then the two continuities in the order they are applied.
-/

def Homeomorphism.trans {X : Type u} {Y : Type v} {Z : Type w} {T : Topology X}
    {T' : Topology Y} {T'' : Topology Z} (h : Homeomorphism T T') (h' : Homeomorphism T' T'') :
    Homeomorphism T T'' where
  toFun := h'.toFun ∘ h.toFun
  invFun := h.invFun ∘ h'.invFun
  left_inv := fun x => by
    show h.invFun (h'.invFun (h'.toFun (h.toFun x))) = x
    rw [h'.left_inv, h.left_inv]
  right_inv := fun z => by
    show h'.toFun (h.toFun (h.invFun (h'.invFun z))) = z
    rw [h.right_inv, h'.right_inv]
  continuous_toFun := Topology.continuous_comp T h.continuous_toFun h'.continuous_toFun
  continuous_invFun := Topology.continuous_comp T'' h'.continuous_invFun h.continuous_invFun

/-- @spec -/
example (X Y Z : Type) (T : Topology X) (T' : Topology Y) (T'' : Topology Z)
    (h : Homeomorphism T T') (h' : Homeomorphism T' T'') (x : X) (z : Z) :
    (h.trans h').toFun x = h'.toFun (h.toFun x)
      ∧ (h.trans h').invFun z = h.invFun (h'.invFun z) := ⟨rfl, rfl⟩

/-! @end -/

/-!
@problem define_homeomorphic
@title Being Homeomorphic is an Equivalence Relation
@concept homeomorphism

@preamble
A homeomorphism is data — a particular pair of maps — and usually one wants only the fact that some such pair exists. Two spaces are *homeomorphic* when there is a homeomorphism between them.

`Nonempty A` is the proposition that the type `A` has at least one term. It is proved by `⟨a⟩`, and a term is taken back out by `obtain ⟨a⟩ := h`, which is allowed because what is being proved is itself a proposition.

The three constructions above then say that this relation is reflexive, symmetric and transitive.
@description
Define `Homeomorphic T T'` as `Nonempty (Homeomorphism T T')`, and prove the three properties. Each is one line: take the homeomorphisms out of the hypotheses with `obtain`, build the new one with `Homeomorphism.refl`, `.symm` or `.trans`, and wrap it in `⟨_⟩`.
-/

def Homeomorphic {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) : Prop :=
  Nonempty (Homeomorphism T T')

theorem Homeomorphic.refl {X : Type u} (T : Topology X) : Homeomorphic T T :=
  ⟨Homeomorphism.refl T⟩

theorem Homeomorphic.symm {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphic T T') : Homeomorphic T' T := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem Homeomorphic.trans {X : Type u} {Y : Type v} {Z : Type w} {T : Topology X}
    {T' : Topology Y} {T'' : Topology Z} (h : Homeomorphic T T') (h' : Homeomorphic T' T'') :
    Homeomorphic T T'' := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e.trans e'⟩

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) :
    Homeomorphic T T' ↔ Nonempty (Homeomorphism T T') := Iff.rfl

/-! @end -/

/-!
@concept open_closed_maps
@title Open Maps and Closed Maps
@kind definition

Continuity is a condition on preimages and says nothing about images: a continuous map may well carry an open set to a set that is not open. The maps that do carry open sets to open sets, or closed to closed, deserve a name of their own, and the first thing the name is good for is a test telling which continuous bijections are homeomorphisms.
-/

/-!
@problem define_open_closed_map
@title Maps That Carry Open Sets to Open Sets
@concept open_closed_maps

@preamble
A continuous map `f` is an *open map* when the image of every open set is open, and a *closed map* when the image of every closed set is closed.

Neither follows from continuity, and neither implies the other. The two conditions are stated on images, where continuity is stated on preimages, and that is the whole difference between them.

We write `f '' U` for the image `{y | ∃ x ∈ U, f x = y}`, and a membership `y ∈ f '' U` is taken apart by `rintro ⟨x, hx, rfl⟩`.
@description
Define `Topology.IsOpenMap` and `Topology.IsClosedMap`, each taking a topology `T` on `X`, a topology `T'` on `Y` and a map `f : X → Y`. Neither definition asks for continuity; it is a separate hypothesis wherever both are wanted.
-/

def Topology.IsOpenMap {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    (f : X → Y) : Prop :=
  ∀ U, T.IsOpen U → T'.IsOpen (f '' U)

def Topology.IsClosedMap {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    (f : X → Y) : Prop :=
  ∀ C, T.IsClosed C → T'.IsClosed (f '' C)

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (f : X → Y) :
    (T.IsOpenMap T' f ↔ ∀ U, T.IsOpen U → T'.IsOpen (f '' U))
      ∧ (T.IsClosedMap T' f ↔ ∀ C, T.IsClosed C → T'.IsClosed (f '' C)) := ⟨Iff.rfl, Iff.rfl⟩

/-! @end -/

/-!
@problem image_eq_preimage
@title An Image is a Preimage Under the Inverse
@concept open_closed_maps

@preamble
Let `f` and `g` be maps in opposite directions that undo each other. Then the image of a set under `f` is the preimage of that set under `g`.

A point `y` lies in `f '' U` when `y = f x` for some `x` of `U`; applying `g` gives `g y = x`, so `g y` lies in `U`. Conversely, if `g y` lies in `U` then `y` is the image of `g y`, since `f (g y) = y`.

This one equation is why a homeomorphism is well behaved on images as well as preimages, which is what the rest of this concept rests on.
@description
Prove `image_eq_preimage_of_inverse`, for maps `f` and `g` whose composites in both orders are the identity, and then read off `Homeomorphism.image_eq_preimage`. In the first, `Set.ext` reduces to a membership at each point; `show` restates each side as what it abbreviates before rewriting.
-/

theorem image_eq_preimage_of_inverse {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (U : Set X) : f '' U = g ⁻¹' U := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show g (f x) ∈ U
    rw [hgf]
    exact hx
  · intro hy
    exact ⟨g y, hy, hfg y⟩

theorem Homeomorphism.image_eq_preimage {X : Type u} {Y : Type v} {T : Topology X}
    {T' : Topology Y} (h : Homeomorphism T T') (U : Set X) : h.toFun '' U = h.invFun ⁻¹' U :=
  image_eq_preimage_of_inverse h.left_inv h.right_inv U

/-! @end -/

/-!
@problem homeomorphism_open_closed
@title A Homeomorphism is Open and Closed
@concept open_closed_maps

@preamble
The image of an open set under a homeomorphism is the preimage of that set under the inverse, and the inverse is continuous, so the image is open. The closed case is the same sentence with a complement moved across the preimage.

So a homeomorphism is both an open map and a closed map — which is to say that it carries the topology of its source onto the topology of its target, and not merely into it.
@description
Show that the forward map of a homeomorphism is an open map and a closed map. Rewrite the image as a preimage and apply the continuity of the inverse. For the closed case, `show T'.IsOpen _` names the goal, and `Set.preimage_compl` moves the complement inside the preimage where the hypothesis has it.
-/

theorem Homeomorphism.isOpenMap {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphism T T') : T.IsOpenMap T' h.toFun := by
  intro U hU
  rw [h.image_eq_preimage]
  exact h.continuous_invFun U hU

theorem Homeomorphism.isClosedMap {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphism T T') : T.IsClosedMap T' h.toFun := by
  intro C hC
  show T'.IsOpen _
  rw [h.image_eq_preimage, ← Set.preimage_compl]
  exact h.continuous_invFun Cᶜ hC

/-! @end -/

/-!
@problem homeomorphism_of_open_map
@title A Continuous Open Bijection is a Homeomorphism
@concept open_closed_maps

@preamble
The converse holds, and it is the useful direction: to build a homeomorphism it is enough to have a continuous bijection that is an open map. The inverse map's continuity comes for free, because a preimage under the inverse is an image under the map.

A bijection is presented here as it is everywhere in this section — by the map `g` that undoes it, in both orders. Then `g ⁻¹' U` is `f '' U`, which the open-map hypothesis calls open, and that is exactly the continuity of `g`.
@description
Define `Homeomorphism.ofOpenMap`, building a homeomorphism from a continuous open map `f` and a two-sided inverse `g`. Four of the six fields are hypotheses already; for the last, rewrite the preimage backwards with `image_eq_preimage_of_inverse` and apply the open-map hypothesis.
-/

def Homeomorphism.ofOpenMap {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    {f : X → Y} {g : Y → X} (hf : T.Continuous T' f) (hopen : T.IsOpenMap T' f)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Homeomorphism T T' where
  toFun := f
  invFun := g
  left_inv := hgf
  right_inv := hfg
  continuous_toFun := hf
  continuous_invFun := by
    intro U hU
    rw [← image_eq_preimage_of_inverse hgf hfg U]
    exact hopen U hU

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (f : X → Y) (g : Y → X)
    (hf : T.Continuous T' f) (hopen : T.IsOpenMap T' f)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (x : X) (y : Y) :
    (Homeomorphism.ofOpenMap hf hopen hgf hfg).toFun x = f x
      ∧ (Homeomorphism.ofOpenMap hf hopen hgf hfg).invFun y = g y := ⟨rfl, rfl⟩

/-! @end -/

/-!
@concept metric_equivalence
@title Equivalent Metrics
@kind theorem

A topology remembers less than a metric does. Two metrics on one set, each of whose balls contain balls of the other about the same point, call exactly the same subsets open, so the identity map is a homeomorphism between the spaces they give. The first section's two lengths on the plane stand in that relation, and this is what those measurements were for.
-/

/-!
@problem define_metric_equivalent
@title The Definition of Equivalent Metrics
@concept metric_equivalence

@preamble
Two metrics on the same set are *equivalent* when each one's balls contain balls of the other: inside every ball of `M` about a point there is a ball of `N` about that point, and inside every ball of `N` there is a ball of `M`.

Nothing is said about the radii except that they are positive. The taxicab ball of radius `ε` sits inside the supremum ball of radius `ε`, and the supremum ball of radius `ε / 2` sits inside the taxicab ball of radius `ε`; the two radii differ, and the definition does not care.
@description
Define `Metric.Equivalent M N`, a conjunction of two statements: for every point `x` and every `ε > 0` some `N`-ball about `x` lies inside `M.ball x ε`, and for every `x` and `ε > 0` some `M`-ball about `x` lies inside `N.ball x ε`. Put the two in that order.
-/

def Metric.Equivalent {X : Type u} (M N : Metric X) : Prop :=
  (∀ x ε, 0 < ε → ∃ δ > 0, N.ball x δ ⊆ M.ball x ε) ∧
    (∀ x ε, 0 < ε → ∃ δ > 0, M.ball x δ ⊆ N.ball x ε)

/-- @spec -/
example (X : Type) (M N : Metric X) :
    M.Equivalent N ↔ (∀ x ε, 0 < ε → ∃ δ > 0, N.ball x δ ⊆ M.ball x ε)
      ∧ (∀ x ε, 0 < ε → ∃ δ > 0, M.ball x δ ⊆ N.ball x ε) := Iff.rfl

/-! @end -/

/--
@problem is_open_set_of_ball_subset
@title Half of the Comparison Already Moves the Open Sets
@concept metric_equivalence

@preamble
Only one of the two containments is needed to carry openness in one direction, and it is worth isolating, since the theorem below is then this lemma applied twice.

Suppose every ball of `M` contains a ball of `N` about the same point, and let `U` be open for `M`. A point `x` of `U` has an `M`-ball of some radius `ε` inside `U`; inside that ball there is an `N`-ball about `x`; and that `N`-ball is inside `U`. So `U` is open for `N`.
@description
Prove that `U` is open for `N` whenever it is open for `M`, given that every `M.ball x ε` with `ε > 0` contains some `N.ball x δ` with `δ > 0`. Take the radius `U`'s openness supplies, then the radius the hypothesis supplies for it, and offer the second; a point of the smaller ball travels through the larger one into `U`.
-/
theorem Metric.isOpenSet_of_ball_subset {X : Type u} {M N : Metric X}
    (h : ∀ x ε, 0 < ε → ∃ δ > 0, N.ball x δ ⊆ M.ball x ε) {U : Set X}
    (hU : M.IsOpenSet U) : N.IsOpenSet U := by
  intro x hx
  obtain ⟨ε, hε, hsub⟩ := hU x hx
  obtain ⟨δ, hδ, hball⟩ := h x ε hε
  exact ⟨δ, hδ, fun y hy => hsub (hball hy)⟩

/-!
@problem equivalent_homeomorphism
@title Equivalent Metrics Give the Same Space
@concept metric_equivalence

@preamble
Equivalent metrics call the same sets open, by the previous problem in each direction. So the two topologies they induce have the same open sets, and the identity map carries one to the other continuously both ways.

The spaces are therefore homeomorphic without any map being chosen: the points were never moved. What the two metrics disagree about — how far apart two points are — is precisely what the topology has dropped.
@description
Prove `Metric.Equivalent.isOpenSet_iff`, that equivalent metrics agree on which sets are open, and then define `Metric.Equivalent.toHomeomorphism`, the identity as a homeomorphism between the induced topologies. Both of its maps are `id` and both inverse conditions are `rfl`; each continuity is one direction of the equivalence just proved.
-/

theorem Metric.Equivalent.isOpenSet_iff {X : Type u} {M N : Metric X} (h : M.Equivalent N)
    (U : Set X) : M.IsOpenSet U ↔ N.IsOpenSet U :=
  ⟨fun hU => Metric.isOpenSet_of_ball_subset h.1 hU,
   fun hU => Metric.isOpenSet_of_ball_subset h.2 hU⟩

def Metric.Equivalent.toHomeomorphism {X : Type u} {M N : Metric X} (h : M.Equivalent N) :
    Homeomorphism M.toTopology N.toTopology where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := fun U hU => (h.isOpenSet_iff U).mpr hU
  continuous_invFun := fun U hU => (h.isOpenSet_iff U).mp hU

/-- @spec -/
example (X : Type) (M N : Metric X) (h : M.Equivalent N) (x : X) :
    h.toHomeomorphism.toFun x = x ∧ h.toHomeomorphism.invFun x = x := ⟨rfl, rfl⟩

/-! @end -/

/-!
@problem plane_metrics_homeomorphic
@title The Two Planes Are One Space
@concept metric_equivalence

@preamble
The first section measured the plane twice. The taxicab length adds the magnitudes of the coordinates and the supremum length takes the larger of them; their unit balls are a diamond and a square, and a point was found in one and not the other.

It also proved the two containments this concept asks for: a taxicab ball of radius `ε` lies inside the supremum ball of radius `ε`, and a supremum ball of radius `ε / 2` lies inside the taxicab ball of radius `ε`. So the two metrics are equivalent, and the two planes are the same topological space.
@description
Show that the taxicab and supremum metrics on the plane are equivalent, and hence that the spaces they give are homeomorphic. Each half of the equivalence offers a radius — `ε / 2` for one and `ε` for the other — and cites `ball_supNorm_subset_taxicab` or `ball_taxicab_subset_supNorm`.
-/

theorem taxicab_equivalent_supNorm : taxicab.toMetric.Equivalent supNorm.toMetric := by
  constructor
  · intro x ε hε
    exact ⟨ε / 2, by linarith, ball_supNorm_subset_taxicab x ε⟩
  · intro x ε hε
    exact ⟨ε, hε, ball_taxicab_subset_supNorm x ε⟩

theorem plane_homeomorphic :
    Homeomorphic taxicab.toMetric.toTopology supNorm.toMetric.toTopology :=
  ⟨taxicab_equivalent_supNorm.toHomeomorphism⟩

/-! @end -/

/-!
@concept topological_invariants
@title Telling Two Spaces Apart
@kind theorem
@goal

To show that two spaces are the same one exhibits a homeomorphism. To show that they are not, one needs a property that homeomorphic spaces must share, and then finds it on one side and not on the other. Two such properties settle the three topologies a two-point set carries, and with them the subject can say that spaces differ, and not only that they agree.
-/

/-!
@problem homeomorphism_is_open_iff
@title A Homeomorphism Carries the Open Sets Across
@concept topological_invariants

@preamble
Everything a topology knows is which sets are open, so any property shared by homeomorphic spaces must come from a correspondence between the two families of open sets. Here it is.

A homeomorphism's two maps undo each other on sets as well as on points: the preimage under the inverse of the preimage under the map is the set one started with. With that, a set of `Y` is open exactly when its preimage in `X` is open — forwards by the continuity of the map, backwards by the continuity of the inverse.
@description
Prove the two. The first is a set equality at each point, restated with `show` and closed by rewriting with `h.right_inv`. In the second, the forward direction is the continuity of the map; the backward direction applies the continuity of the inverse and rewrites its conclusion by the first.
-/

theorem Homeomorphism.preimage_preimage {X : Type u} {Y : Type v} {T : Topology X}
    {T' : Topology Y} (h : Homeomorphism T T') (V : Set Y) :
    h.invFun ⁻¹' (h.toFun ⁻¹' V) = V := by
  apply Set.ext
  intro y
  show h.toFun (h.invFun y) ∈ V ↔ y ∈ V
  rw [h.right_inv]

theorem Homeomorphism.isOpen_iff {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphism T T') (V : Set Y) : T'.IsOpen V ↔ T.IsOpen (h.toFun ⁻¹' V) := by
  constructor
  · intro hV
    exact h.continuous_toFun V hV
  · intro hV
    have hp := h.continuous_invFun _ hV
    rwa [h.preimage_preimage] at hp

/-! @end -/

/-!
@problem define_discrete_codiscrete
@title Two Properties of a Space
@concept topological_invariants

@preamble
The two extreme topologies of the third section were built; now the same two descriptions are read as properties that an arbitrary space may or may not have.

A space is *discrete* when every subset is open, and *codiscrete* when the only open subsets are the empty one and the whole space. A space may be both, if it has at most one point, and most spaces are neither.

The discrete topology is discrete and the codiscrete topology is codiscrete, which is what the names were chosen to make true.
@description
Define `Topology.IsDiscrete` and `Topology.IsCodiscrete`, and then show that `discrete X` has the first property and `codiscrete X` the second. Both proofs are the definition unfolding: nothing has to be done to what `discrete` and `codiscrete` already say.
-/

def Topology.IsDiscrete {X : Type u} (T : Topology X) : Prop := ∀ U, T.IsOpen U

def Topology.IsCodiscrete {X : Type u} (T : Topology X) : Prop :=
  ∀ U, T.IsOpen U → U = ∅ ∨ U = Set.univ

theorem discrete_isDiscrete (X : Type u) : (discrete X).IsDiscrete := fun _ => trivial

theorem codiscrete_isCodiscrete (X : Type u) : (codiscrete X).IsCodiscrete := fun _ hU => hU

/-- @spec -/
example (X : Type) (T : Topology X) :
    (T.IsDiscrete ↔ ∀ U, T.IsOpen U)
      ∧ (T.IsCodiscrete ↔ ∀ U, T.IsOpen U → U = ∅ ∨ U = Set.univ) := ⟨Iff.rfl, Iff.rfl⟩

/-! @end -/

/-!
@problem invariants_transport
@title Both Properties Are Topological Invariants
@concept topological_invariants

@preamble
A property is a *topological invariant* when homeomorphic spaces either both have it or both lack it. Discreteness and codiscreteness are two, and the correspondence between the open sets is the whole proof of each.

For discreteness: a set of `Y` is open when its preimage is, and upstairs every set is open. For codiscreteness: the preimage of an open set is open, hence empty or everything, and taking the preimage back under the inverse returns the set one started with — empty or everything accordingly.
@description
Prove that a space homeomorphic to a discrete space is discrete, and that a space homeomorphic to a codiscrete space is codiscrete. Take the homeomorphism out with `obtain`, and use `isOpen_iff` in each. For the second, rewrite the goal backwards with `preimage_preimage` before rewriting by the case in hand.
-/

theorem Homeomorphic.isDiscrete {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphic T T') (hT : T.IsDiscrete) : T'.IsDiscrete := by
  obtain ⟨e⟩ := h
  intro V
  exact (e.isOpen_iff V).mpr (hT _)

theorem Homeomorphic.isCodiscrete {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphic T T') (hT : T.IsCodiscrete) : T'.IsCodiscrete := by
  obtain ⟨e⟩ := h
  intro V hV
  rcases hT _ ((e.isOpen_iff V).mp hV) with he | he
  · left
    rw [← e.preimage_preimage V, he, Set.preimage_empty]
  · right
    rw [← e.preimage_preimage V, he, Set.preimage_univ]

/-! @end -/

/-!
@problem sierpinski_is_neither
@title The Sierpiński Space Has Neither Property
@concept topological_invariants

@preamble
A two-point set carries the two extreme topologies and the Sierpiński topology, and the invariants will tell the three apart once it is known which space has which property.

The Sierpiński space is not discrete, since `{false}` is not open in it — that was the point of the example. It is not codiscrete either, since `{true}` is open in it and is neither empty nor everything.

The set `{true}` is where both failures are read, so it is worth recording once that it is not one of the two trivial subsets of `Bool`.
@description
Show that `{true}` is neither `∅` nor `Set.univ` as a subset of `Bool`, and that `sierpinski` is neither discrete nor codiscrete. For the first, a membership of `true` refutes the empty case and a membership of `false` the other; the openness of `{true}` in `sierpinski` is an implication whose hypothesis is not needed.
-/

theorem singleton_true_not_trivial :
    ¬ (({true} : Set Bool) = ∅ ∨ ({true} : Set Bool) = Set.univ) := by
  rintro (he | he)
  · have h : (true : Bool) ∈ ({true} : Set Bool) := rfl
    rw [he] at h
    exact h
  · have h : (false : Bool) ∈ ({true} : Set Bool) := by rw [he]; trivial
    exact Bool.noConfusion h

theorem sierpinski_not_discrete : ¬ sierpinski.IsDiscrete := fun h =>
  sierpinski_singleton_false_not_open (h {false})

theorem sierpinski_not_codiscrete : ¬ sierpinski.IsCodiscrete := fun h =>
  singleton_true_not_trivial (h {true} (fun _ => rfl))

/-! @end -/

/-!
@problem two_point_topologies
@title Three Spaces on Two Points, No Two the Same
@concept topological_invariants

@preamble
Now the three are separated. The discrete space is discrete and neither of the others is, which distinguishes it from both; the codiscrete space is codiscrete and the Sierpiński space is not, which distinguishes those two.

One consequence is worth stating. The identity map from the discrete space to the codiscrete space on `Bool` is a continuous bijection: every map out of a discrete space is continuous, and the identity is its own inverse. Yet the two spaces are not homeomorphic, so a continuous bijection need not be one — which is why the open-map hypothesis was needed above.
@description
Prove that no two of `discrete Bool`, `codiscrete Bool` and `sierpinski` are homeomorphic. Each proof transports one of the two invariants along the assumed homeomorphism and contradicts a fact from the previous problems.
-/

theorem discrete_not_homeomorphic_codiscrete :
    ¬ Homeomorphic (discrete Bool) (codiscrete Bool) := by
  intro h
  exact singleton_true_not_trivial (h.isDiscrete (discrete_isDiscrete Bool) {true})

theorem discrete_not_homeomorphic_sierpinski :
    ¬ Homeomorphic (discrete Bool) sierpinski := by
  intro h
  exact sierpinski_not_discrete (h.isDiscrete (discrete_isDiscrete Bool))

theorem codiscrete_not_homeomorphic_sierpinski :
    ¬ Homeomorphic (codiscrete Bool) sierpinski := by
  intro h
  exact sierpinski_not_codiscrete (h.isCodiscrete (codiscrete_isCodiscrete Bool))

/-! @end -/

end GeneralTopology
