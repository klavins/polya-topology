import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Homeomorphisms

/-! @section Subspaces and Products -/

universe u v w

namespace GeneralTopology

/-!
@concept subspace_maps
@title Maps and a Subspace
@kind theorem

A subset of a space carries the topology cut out of the ambient open sets. What that buys is a test for maps: a map into the subset is continuous exactly when the same map read into the whole space is, so a subspace is never examined directly. Its closed sets are cut out the same way.
-/

/--
@problem subspace_universal
@title A Map Into a Subspace
@concept subspace_maps

@preamble
A subset `A` of a space `X` is a space in its own right, and `Subtype.val` puts its points back into `X`. That inclusion is continuous, which is what the subspace topology was defined to arrange. The question left is the other one: given a map `g` from a space `Z` into `A`, when is `g` continuous?

Nothing beyond `X` need be looked at. Following `g` by the inclusion gives a map `Z → X`, and `g` is continuous exactly when that composite is. One direction is the composition law. The other is the definition read backwards: an open set of `A` is `Subtype.val ⁻¹' U` for an open `U` of `X`, and its preimage under `g` is the preimage of `U` under the composite.
@description
Prove that `S.Continuous (T.subspace A) g` exactly when `S.Continuous T (Subtype.val ∘ g)`. Forwards, compose with `Topology.continuous_subspace_val`. Backwards, take the open set apart with `obtain ⟨U, hU, rfl⟩` and fold the two preimages into one with `Set.preimage_comp`.
-/
theorem Topology.continuous_into_subspace {X : Type u} {Z : Type v} (T : Topology X) (A : Set X)
    (S : Topology Z) (g : Z → A) :
    S.Continuous (T.subspace A) g ↔ S.Continuous T (Subtype.val ∘ g) := by
  constructor
  · intro hg
    exact Topology.continuous_comp S hg (Topology.continuous_subspace_val T A)
  · intro hg U hU
    obtain ⟨V, hV, rfl⟩ := hU
    rw [← Set.preimage_comp]
    exact hg V hV

/--
@problem subspace_corestrict
@title Restricting the Target
@concept subspace_maps

@preamble
A map may happen to take all of its values in a subset of its target, and it ought then to count as a map into that subset. Written in Lean the two are not the same map: a point of `A` is a point of `Y` carrying a proof that it lies in `A`, so the second map is `fun x => (⟨f x, h x⟩ : A)`, which pairs each value with that proof.

Continuity survives the change, for the reason the last problem gave. An open set of `A` is the trace of an open `U`, and the points whose image lands in the trace are exactly the points whose image lands in `U`.
@description
Show that `fun x => (⟨f x, h x⟩ : A)` is continuous into `T'.subspace A` when `f` is continuous and every `f x` lies in `A`. Take the open set apart with `obtain ⟨U, hU, rfl⟩`; what is left is the hypothesis at `U`, with no rewriting needed.
-/
theorem Topology.continuous_toSubspace {X : Type u} {Y : Type v} {T : Topology X}
    {T' : Topology Y} {f : X → Y} (hf : T.Continuous T' f) (A : Set Y) (h : ∀ x, f x ∈ A) :
    T.Continuous (T'.subspace A) (fun x => (⟨f x, h x⟩ : A)) := by
  intro V hV
  obtain ⟨U, hU, rfl⟩ := hV
  exact hf U hU

/--
@problem subspace_closed_sets
@title The Closed Sets of a Subspace
@concept subspace_maps

@preamble
The open sets of a subspace are the traces of the open sets. The closed sets are the traces of the closed sets, and that is the same statement read through complements — but the reading has a step in it, since the complement is taken inside `A` on one side and inside `X` on the other.

If `V` is closed in `A` then `Vᶜ` is the trace of an open `U`, and `V` is then the trace of `Uᶜ`, because a preimage commutes with complementing. The other direction runs backwards along the same equation.
@description
Prove that `V` is closed in `T.subspace A` exactly when `V = Subtype.val ⁻¹' C` for some closed `C` of `X`. `Set.preimage_compl` moves a complement across a preimage, and `compl_compl` cancels the pair that appears on each side.
-/
theorem Topology.isClosed_subspace_iff {X : Type u} (T : Topology X) (A : Set X) (V : Set A) :
    (T.subspace A).IsClosed V ↔ ∃ C, T.IsClosed C ∧ V = Subtype.val ⁻¹' C := by
  constructor
  · rintro ⟨U, hU, hVU⟩
    refine ⟨Uᶜ, ?_, ?_⟩
    · show T.IsOpen Uᶜᶜ
      rwa [compl_compl]
    · rw [Set.preimage_compl, ← hVU, compl_compl]
  · rintro ⟨C, hC, rfl⟩
    show (T.subspace A).IsOpen _
    refine ⟨Cᶜ, hC, ?_⟩
    rw [Set.preimage_compl]

/-!
@concept induced_topology
@title The Induced Topology
@kind definition

The subspace topology pulls the open sets of a space back along an inclusion. Nothing in that used the map to be an inclusion, and the same construction along an arbitrary map is the coarsest topology making that map continuous. Naming it makes the subspace one case rather than a separate definition, and it is the shape every later construction of a space from a map takes.
-/

/-!
@problem define_induced
@title The Topology Induced by a Map
@concept induced_topology

@preamble
Let `f` carry a set `X` to a space `Y`. Call a subset of `X` open when it is the preimage of an open set of `Y`. This is a topology, and the three conditions hold because preimages commute with the three operations: the preimage of the whole space is the whole space, the preimage of an intersection is the intersection of the preimages, and the preimage of a union is the union of the preimages.

The subspace topology is this construction with `f` the inclusion. The two are then not merely equivalent but the same term, so `rfl` proves it.
@description
Define `Topology.induced`, the topology on `X` whose open sets are the preimages under `f` of the open sets of `T`, and show that `T.subspace A` is `T.induced Subtype.val`. Follow the fields of `Topology.subspace`: the last offers the union of those open sets of `Y` whose preimage belongs to the given collection.
-/

def Topology.induced {X : Type u} {Y : Type v} (T : Topology Y) (f : X → Y) : Topology X where
  IsOpen := fun V => ∃ U, T.IsOpen U ∧ V = f ⁻¹' U
  univ := ⟨Set.univ, T.univ, rfl⟩
  inter := by
    rintro V W ⟨U, hU, rfl⟩ ⟨U', hU', rfl⟩
    exact ⟨U ∩ U', T.inter hU hU', rfl⟩
  sUnion := by
    intro F h
    refine ⟨⋃₀ {U | T.IsOpen U ∧ (f ⁻¹' U : Set X) ∈ F}, T.sUnion (fun U hU => hU.1), ?_⟩
    apply Set.Subset.antisymm
    · rintro x ⟨V, hVF, hxV⟩
      obtain ⟨U, hU, rfl⟩ := h V hVF
      exact ⟨U, ⟨hU, hVF⟩, hxV⟩
    · rintro x ⟨U, ⟨hU, hUF⟩, hxU⟩
      exact ⟨_, hUF, hxU⟩

theorem Topology.subspace_eq_induced {X : Type u} (T : Topology X) (A : Set X) :
    T.subspace A = T.induced (Subtype.val : A → X) := rfl

/-- @spec -/
example (X Y : Type) (T : Topology Y) (f : X → Y) (V : Set X) :
    (T.induced f).IsOpen V ↔ ∃ U, T.IsOpen U ∧ V = f ⁻¹' U := Iff.rfl

/-! @end -/

/-!
@problem induced_continuous
@title The Coarsest Topology Making a Map Continuous
@concept induced_topology

@preamble
The induced topology was built to make `f` continuous, and it does, with nothing to check: the preimage of an open set is a preimage of an open set.

It is the smallest topology that does. If `S` is any topology on `X` for which `f` is continuous, then `S` calls open everything the induced topology calls open, since each of those is the preimage of an open set. So the induced topology puts on `X` exactly the open sets that `f` forces, and no others.
@description
Show that `f` is continuous from `T.induced f` to `T`, and that any topology `S` making `f` continuous calls open every set that `T.induced f` calls open. Each is one line once the open set has been taken apart.
-/

theorem Topology.continuous_induced {X : Type u} {Y : Type v} (T : Topology Y) (f : X → Y) :
    (T.induced f).Continuous T f :=
  fun U hU => ⟨U, hU, rfl⟩

theorem Topology.induced_coarsest {X : Type u} {Y : Type v} {T : Topology Y} {S : Topology X}
    {f : X → Y} (hf : S.Continuous T f) {V : Set X} (hV : (T.induced f).IsOpen V) : S.IsOpen V := by
  obtain ⟨U, hU, rfl⟩ := hV
  exact hf U hU

/-! @end -/

/--
@problem topology_eq_of_opens
@title Topologies Agreeing on Open Sets Are Equal
@concept induced_topology

@preamble
A topology carries three proofs beside its family of open sets, and proofs are not data: two proofs of one proposition are equal. So two topologies on a set are equal as soon as they call the same subsets open, and there is never anything else to compare.

Taking a structure apart with `obtain` leaves its four fields as separate hypotheses. Once the two families of open sets are shown equal, substituting one for the other makes the remaining fields proofs of the very same statements, and the two structures are then the same term.
@description
Prove that `T = T'` whenever `T.IsOpen U ↔ T'.IsOpen U` for every `U`. Take both topologies apart with `obtain ⟨o, hu, hi, hs⟩ := T`, prove the two families equal with `funext` and `propext`, substitute with `subst`, and close with `rfl`.
-/
theorem Topology.eq_of_isOpen_iff {X : Type u} {T T' : Topology X}
    (h : ∀ U, T.IsOpen U ↔ T'.IsOpen U) : T = T' := by
  obtain ⟨o, hu, hi, hs⟩ := T
  obtain ⟨o', hu', hi', hs'⟩ := T'
  have e : o = o' := funext (fun U => propext (h U))
  subst e
  rfl

/--
@problem induced_comp
@title Inducing Twice
@concept induced_topology

@preamble
A subspace of a subspace is a subspace of the space they both sit in, and the general statement is about maps: inducing along `f` and then along `g` is inducing along `f ∘ g`.

Each side calls a set open when it is a preimage of an open set of `Z` — on the left along `g` and then along `f`, on the right along the composite at once. That preimages compose is the whole of the proof.
@description
Prove `(T.induced f).induced g = T.induced (f ∘ g)`. The previous problem reduces it to an equivalence at each set; `Set.preimage_comp` closes one direction and its symmetric form the other.
-/
theorem Topology.induced_induced {X : Type u} {Y : Type v} {Z : Type w} (T : Topology Z)
    (f : Y → Z) (g : X → Y) : (T.induced f).induced g = T.induced (f ∘ g) := by
  apply Topology.eq_of_isOpen_iff
  intro V
  constructor
  · rintro ⟨W, ⟨U, hU, rfl⟩, rfl⟩
    exact ⟨U, hU, Set.preimage_comp.symm⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨f ⁻¹' U, ⟨U, hU, rfl⟩, Set.preimage_comp⟩

/-!
@concept product_topology
@title The Product Topology
@kind definition

Two spaces have a product set, and it should be a space. A point of it is a pair, and the room around a pair is a pair of rooms: a set is open when each of its points has an open box around it inside. This is the first construction of a space from two others, and what the subject later says about separation, compactness and the plane is said in it.
-/

/-!
@problem define_product
@title The Product of Two Spaces
@concept product_topology

@preamble
Let `T` be a topology on `X` and `T'` one on `Y`. A *box* is a set `U ×ˢ V` with `U` a subset of `X` and `V` a subset of `Y`; a pair belongs to it when its two coordinates belong to the two sides, which is what `p ∈ U ×ˢ V` unfolds to.

Call a subset `W` of `X × Y` open when every point of it has an open box around it inside `W`. This is the definition of an open set of a metric space with a box in place of a ball, and the three conditions come out as they did there: the whole space is a box, two boxes meet in a box, and a box inside one member of a union is inside the union.
@description
Define `Topology.prod`, the product topology on `X × Y`. Its `IsOpen W` says that for every `p ∈ W` there are `U` and `V` with four properties in this order: `U` is open, `V` is open, `p ∈ U ×ˢ V`, and `U ×ˢ V ⊆ W`. For the intersection field the box wanted is the two boxes intersected a side at a time, `U ∩ U'` against `V ∩ V'`.
-/

def Topology.prod {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    Topology (X × Y) where
  IsOpen := fun W => ∀ p ∈ W, ∃ U V, T.IsOpen U ∧ T'.IsOpen V ∧ p ∈ U ×ˢ V ∧ U ×ˢ V ⊆ W
  univ := fun _ _ => ⟨Set.univ, Set.univ, T.univ, T'.univ, ⟨trivial, trivial⟩, fun _ _ => trivial⟩
  inter := by
    rintro W W' hW hW' p hp
    obtain ⟨U, V, hU, hV, hpUV, hsub⟩ := hW p hp.1
    obtain ⟨U', V', hU', hV', hpUV', hsub'⟩ := hW' p hp.2
    refine ⟨U ∩ U', V ∩ V', T.inter hU hU', T'.inter hV hV',
      ⟨⟨hpUV.1, hpUV'.1⟩, ⟨hpUV.2, hpUV'.2⟩⟩, ?_⟩
    rintro q ⟨hq1, hq2⟩
    exact ⟨hsub ⟨hq1.1, hq2.1⟩, hsub' ⟨hq1.2, hq2.2⟩⟩
  sUnion := by
    rintro F h p ⟨W, hWF, hpW⟩
    obtain ⟨U, V, hU, hV, hpUV, hsub⟩ := h W hWF p hpW
    exact ⟨U, V, hU, hV, hpUV, fun q hq => ⟨W, hWF, hsub hq⟩⟩

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (W : Set (X × Y)) :
    (T.prod T').IsOpen W ↔
      ∀ p ∈ W, ∃ U V, T.IsOpen U ∧ T'.IsOpen V ∧ p ∈ U ×ˢ V ∧ U ×ˢ V ⊆ W := Iff.rfl

/-! @end -/

/--
@problem product_box_open
@title A Box is Open
@concept product_topology

@preamble
The definition asks that each point of an open set have an open box around it inside, so it had better be that a box with open sides is itself open. It is, by the cheapest argument available: the box a point of it needs is the box itself.

That is a difference from the metric case. There a point near the edge of a ball needed a smaller ball, and the triangle inequality had to produce one. A box carries no such obligation, since the condition on a point mentions only membership and containment.
@description
Show that `U ×ˢ V` is open in `T.prod T'` when `U` and `V` are open. The two witnesses are `U` and `V` themselves, the membership is the hypothesis at the point, and the containment is `subset_rfl`.
-/
theorem Topology.isOpen_prod_box {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    {U : Set X} {V : Set Y} (hU : T.IsOpen U) (hV : T'.IsOpen V) :
    (T.prod T').IsOpen (U ×ˢ V) :=
  fun _ hp => ⟨U, V, hU, hV, hp, subset_rfl⟩

/--
@problem product_boxes_union
@title Every Open Set is a Union of Boxes
@concept product_topology

@preamble
Open boxes are to a product what open balls are to a metric. Not every open set is one, but every open set is a union of them, and that is what it means to say the boxes are a basis for the topology.

Collect the open boxes lying inside a set `W` that is open in the product. Each of them is inside `W`, so their union is; and every point of `W` has one of them around it, so the union reaches every point of `W`. The collection is described by a property rather than listed, as a collection of sets always is here.
@description
Show that an open `W` of `T.prod T'` equals `⋃₀ {B | B ⊆ W ∧ ∃ U V, T.IsOpen U ∧ T'.IsOpen V ∧ B = U ×ˢ V}`. `Set.Subset.antisymm` splits it in two; one direction offers the box the definition supplies at the point, and the other applies the containment the member carries.
-/
theorem Topology.prod_eq_sUnion_boxes {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    {W : Set (X × Y)} (hW : (T.prod T').IsOpen W) :
    W = ⋃₀ {B | B ⊆ W ∧ ∃ U V, T.IsOpen U ∧ T'.IsOpen V ∧ B = U ×ˢ V} := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨U, V, hU, hV, hpUV, hsub⟩ := hW p hp
    exact ⟨U ×ˢ V, ⟨hsub, U, V, hU, hV, rfl⟩, hpUV⟩
  · rintro p ⟨B, ⟨hBW, _⟩, hpB⟩
    exact hBW hpB

/-!
@concept product_maps
@title Maps and a Product
@kind theorem

The projections out of a product are continuous, and they are open maps as well, which continuous maps rarely are. In the other direction a map into a product is a pair of maps, one into each factor, and it is continuous exactly when both of them are. With that, the product never has to be examined through its definition again.
-/

/-!
@problem projections_continuous
@title The Projections Are Continuous
@concept product_maps

@preamble
`Prod.fst` sends a pair to its first coordinate and `Prod.snd` to its second. The preimage of a subset `U` of `X` under the first is the slab `U ×ˢ Set.univ`, a box one of whose sides is the whole of `Y`; the preimage of a subset `V` of `Y` under the second is `Set.univ ×ˢ V`. Both are boxes with open sides, hence open, so both projections are continuous.

That a preimage is that box is `Set.prod_univ`, or `Set.univ_prod`, read backwards.
@description
Show that `Prod.fst` and `Prod.snd` are continuous from `T.prod T'`. Rewrite the preimage as a box with `← Set.prod_univ` or `← Set.univ_prod`, and apply the previous problem, with `T'.univ` or `T.univ` for the side that is everything.
-/

theorem Topology.continuous_fst {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    (T.prod T').Continuous T Prod.fst := by
  intro U hU
  rw [← Set.prod_univ]
  exact Topology.isOpen_prod_box T T' hU T'.univ

theorem Topology.continuous_snd {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    (T.prod T').Continuous T' Prod.snd := by
  intro V hV
  rw [← Set.univ_prod]
  exact Topology.isOpen_prod_box T T' T.univ hV

/-! @end -/

/-!
@problem projections_open
@title The Projections Are Open Maps
@concept product_maps

@preamble
A continuous map need not carry open sets to open sets. The projections do.

Let `W` be open in the product and let `p` be a point of it. Some open box `U ×ˢ V` around `p` lies inside `W`. Then `U` lies inside the image of `W` under the first projection, because a point `u` of `U` is the first coordinate of `(u, p.2)`, which is in the box and so in `W`. So the image has an open set around each of its points, which is openness.
@description
Show that `Prod.fst` and `Prod.snd` are open maps from `T.prod T'`. `Topology.isOpen_iff_nbhd` turns the goal into a statement at each point of the image; take that point apart with `rintro x ⟨p, hpW, rfl⟩`, offer the box's side, and name `(u, p.2)` as the point a given `u` comes from.
-/

theorem Topology.isOpenMap_fst {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    (T.prod T').IsOpenMap T Prod.fst := by
  intro W hW
  rw [Topology.isOpen_iff_nbhd]
  rintro x ⟨p, hpW, rfl⟩
  obtain ⟨U, V, hU, hV, hpUV, hsub⟩ := hW p hpW
  exact ⟨U, hU, hpUV.1, fun u hu => ⟨(u, p.2), hsub ⟨hu, hpUV.2⟩, rfl⟩⟩

theorem Topology.isOpenMap_snd {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    (T.prod T').IsOpenMap T' Prod.snd := by
  intro W hW
  rw [Topology.isOpen_iff_nbhd]
  rintro y ⟨p, hpW, rfl⟩
  obtain ⟨U, V, hU, hV, hpUV, hsub⟩ := hW p hpW
  exact ⟨V, hV, hpUV.2, fun v hv => ⟨(p.1, v), hsub ⟨hpUV.1, hv⟩, rfl⟩⟩

/-! @end -/

/-!
@problem product_universal
@title A Map Into a Product is a Pair of Maps
@concept product_maps

@preamble
To give a map from `Z` into `X × Y` is to give a map into `X` and a map into `Y`, since a point of the product is a pair. The topology is chosen so that the same holds of continuity.

One direction is composition with the projections. For the other, let `W` be open in the product and let `z` be a point whose image lies in `W`. A box `U ×ˢ V` around that image lies inside `W`, and `f ⁻¹' U ∩ g ⁻¹' V` is then an open set around `z` inside the preimage of `W`. So the preimage is a neighbourhood of each of its points.
@description
Prove that `fun z => (f z, g z)` is continuous when `f` and `g` are, and then that a map `h : Z → X × Y` is continuous exactly when its two components are. For the second, compose with the projections in one direction; in the other, `h` and the pair of its components are the same map, so the first applies as it stands.
-/

theorem Topology.continuous_prod_mk {X : Type u} {Y : Type v} {Z : Type w} {T : Topology X}
    {T' : Topology Y} (S : Topology Z) {f : Z → X} {g : Z → Y} (hf : S.Continuous T f)
    (hg : S.Continuous T' g) : S.Continuous (T.prod T') (fun z => (f z, g z)) := by
  intro W hW
  rw [Topology.isOpen_iff_nbhd]
  intro z hz
  obtain ⟨U, V, hU, hV, hzUV, hsub⟩ := hW (f z, g z) hz
  refine ⟨f ⁻¹' U ∩ g ⁻¹' V, S.inter (hf U hU) (hg V hV), ⟨hzUV.1, hzUV.2⟩, ?_⟩
  intro w hw
  exact hsub ⟨hw.1, hw.2⟩

theorem Topology.continuous_prod_iff {X : Type u} {Y : Type v} {Z : Type w} (T : Topology X)
    (T' : Topology Y) (S : Topology Z) (h : Z → X × Y) :
    S.Continuous (T.prod T') h ↔
      S.Continuous T (fun z => (h z).1) ∧ S.Continuous T' (fun z => (h z).2) := by
  constructor
  · intro hh
    exact ⟨Topology.continuous_comp S hh (Topology.continuous_fst T T'),
      Topology.continuous_comp S hh (Topology.continuous_snd T T')⟩
  · rintro ⟨hf, hg⟩
    exact Topology.continuous_prod_mk S hf hg

/-! @end -/

/-!
@problem product_slices
@title The Slices of a Product
@concept product_maps

@preamble
Fixing one coordinate lays a factor along the product: `fun x => (x, y)` puts `X` at the level `y`. Such a map is continuous, and the universal property proves it without the definition of the product topology being touched at all — the two components are the identity and a constant, and both were shown continuous in an earlier section.
@description
Show that `fun x => (x, y)` and `fun y => (x, y)` are continuous into `T.prod T'`. Each is the previous problem applied to `Topology.continuous_id` and `Topology.continuous_const`, in the order the coordinates come.
-/

theorem Topology.continuous_mk_left {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    (y : Y) : T.Continuous (T.prod T') (fun x => (x, y)) :=
  Topology.continuous_prod_mk T (Topology.continuous_id T) (Topology.continuous_const T T' y)

theorem Topology.continuous_mk_right {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    (x : X) : T'.Continuous (T.prod T') (fun y => (x, y)) :=
  Topology.continuous_prod_mk T' (Topology.continuous_const T' T x) (Topology.continuous_id T')

/-! @end -/

/-!
@concept plane_is_product
@title The Plane as a Product
@kind theorem
@goal

The plane was built as a set with a distance, the line as a set with a distance, and the two have had no formal relation. The supremum distance is the larger of the two coordinate distances, so a ball of it is a square — a box of two intervals. The plane is therefore the product of two lines, which is where the metric half of the subject meets the topological one.
-/

/--
@problem ball_is_box
@title A Supremum Ball is a Box
@concept plane_is_product

@preamble
The supremum length of a vector is the larger of the magnitudes of its coordinates, so the supremum distance from `x` to `y` is the larger of `|x.1 - y.1|` and `|x.2 - y.2|`. That the larger of two numbers is below `ε` is exactly that both of them are, and each of the two is a membership in a ball of the line.

So a ball of the supremum metric is the box whose sides are the two coordinate balls of the same radius: the square of side `2 * ε` centred at `x`, which is the picture the first section drew of it.
@description
Show that `supNorm.toMetric.ball x ε = line.ball x.1 ε ×ˢ line.ball x.2 ε`. `ext y` reduces the equality to a membership at each point, `show` restates both sides as the inequalities they abbreviate, and `max_lt_iff` is the equivalence that remains.
-/
theorem ball_supNorm_eq_box (x : ℝ × ℝ) (ε : ℝ) :
    supNorm.toMetric.ball x ε = line.ball x.1 ε ×ˢ line.ball x.2 ε := by
  ext y
  show max |x.1 - y.1| |x.2 - y.2| < ε ↔ |x.1 - y.1| < ε ∧ |x.2 - y.2| < ε
  exact max_lt_iff

/-!
@problem plane_opens_agree
@title The Two Topologies Call the Same Sets Open
@concept plane_is_product

@preamble
Each direction fits the balls and the boxes together at a point.

A set open for the supremum metric has a ball inside it around each of its points. The ball is a box, so the point has an open box inside the set, and the set is open in the product.

A set open in the product has a box `U ×ˢ V` inside it around each point `p`. Now `U` contains a ball of the line about `p.1` and `V` one about `p.2`; the smaller of those two radii gives a box that is a single supremum ball, and it lies inside the original box.
@description
Prove both directions between `supNorm.toMetric.IsOpenSet W` and `(line.toTopology.prod line.toTopology).IsOpen W`. The previous problem rewrites a ball as a box in each. For the second, `min a b` is the radius, and `Metric.ball_mono` carries a point of the smaller ball into each of the two.
-/

theorem isOpen_prod_of_isOpenSet_supNorm {W : Set (ℝ × ℝ)} (h : supNorm.toMetric.IsOpenSet W) :
    (line.toTopology.prod line.toTopology).IsOpen W := by
  intro p hp
  obtain ⟨ε, hε, hsub⟩ := h p hp
  refine ⟨line.ball p.1 ε, line.ball p.2 ε, Metric.isOpenSet_ball line p.1 ε,
    Metric.isOpenSet_ball line p.2 ε,
    ⟨Metric.mem_ball_self line p.1 ε hε, Metric.mem_ball_self line p.2 ε hε⟩, ?_⟩
  rw [← ball_supNorm_eq_box]
  exact hsub

theorem isOpenSet_supNorm_of_isOpen_prod {W : Set (ℝ × ℝ)}
    (h : (line.toTopology.prod line.toTopology).IsOpen W) : supNorm.toMetric.IsOpenSet W := by
  intro p hp
  obtain ⟨U, V, hU, hV, hpUV, hsub⟩ := h p hp
  obtain ⟨a, ha, hau⟩ := hU p.1 hpUV.1
  obtain ⟨b, hb, hbv⟩ := hV p.2 hpUV.2
  refine ⟨min a b, lt_min ha hb, ?_⟩
  rw [ball_supNorm_eq_box]
  rintro q ⟨hq1, hq2⟩
  exact hsub ⟨hau (Metric.ball_mono line (min_le_left a b) hq1),
    hbv (Metric.ball_mono line (min_le_right a b) hq2)⟩

/-! @end -/

/-!
@problem plane_as_product
@title The Plane is the Product of Two Lines
@concept plane_is_product

@preamble
The two topologies have the same open sets, so the identity map is continuous in both directions and the two spaces are one space — the argument that made the taxicab and supremum planes one space, with the points again never moved.

The taxicab plane follows with no further work. It was shown homeomorphic to the supremum plane, and being homeomorphic is transitive. So the plane, measured either way, is the product of two copies of the line.
@description
Build `supNorm_prod_homeomorphism`, the identity as a homeomorphism onto the product, and read off that the supremum plane and then the taxicab plane are homeomorphic to `line.toTopology.prod line.toTopology`. Both maps are `id` and both inverse conditions are `rfl`; the last cites `plane_homeomorphic` and `Homeomorphic.trans`.
-/

def supNorm_prod_homeomorphism :
    Homeomorphism supNorm.toMetric.toTopology (line.toTopology.prod line.toTopology) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := fun _ hW => isOpenSet_supNorm_of_isOpen_prod hW
  continuous_invFun := fun _ hW => isOpen_prod_of_isOpenSet_supNorm hW

theorem plane_homeomorphic_product :
    Homeomorphic supNorm.toMetric.toTopology (line.toTopology.prod line.toTopology) :=
  ⟨supNorm_prod_homeomorphism⟩

theorem taxicab_homeomorphic_product :
    Homeomorphic taxicab.toMetric.toTopology (line.toTopology.prod line.toTopology) :=
  Homeomorphic.trans plane_homeomorphic plane_homeomorphic_product

/-- @spec -/
example (p : ℝ × ℝ) :
    supNorm_prod_homeomorphism.toFun p = p ∧ supNorm_prod_homeomorphism.invFun p = p :=
  ⟨rfl, rfl⟩

/-! @end -/

end GeneralTopology
