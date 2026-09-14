import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Compactness

/-! @section Compact Hausdorff Spaces -/

universe u v

namespace GeneralTopology

/-!
@concept compact_in_hausdorff
@title Compact Sets in a Hausdorff Space
@kind theorem

Compactness and the Hausdorff condition pull in opposite directions: one asks that a cover be reducible, the other that points be held apart. A space with both is as well behaved as a space with no distances can be, and the first thing the pair buys is that a compact set is separated by open sets from every point outside it, and is therefore closed.
-/

/--
@problem separating_union
@title Separating a Set From Finitely Many
@concept compact_in_hausdorff

@preamble
Let `A` be a set, and suppose an open set `U` holds `A` and misses `V`, while another open set `U'` holds `A` and misses `V'`. Then `U ∩ U'` holds `A` and misses both: intersecting two open sets is allowed, and what is left still holds everything both of them held.

Finitely many sets are two at a time repeated. This is the shape a compact set forces on every argument of this section — finitely many things, so an intersection of open sets that is still open.
@description
Prove `Topology.exists_nbhd_disjoint_sUnion`: if every member of a finite collection `G` is missed by some open set holding `A`, then one open set holding `A` misses the whole of `⋃₀ G`. The proof is an induction on the finiteness, `induction G, hfin using Set.Finite.induction_on`, with `Set.univ` for the empty collection and `U ∩ U'` for the step; `Set.eq_empty_of_forall_notMem` and `Set.eq_empty_iff_forall_notMem` pass between a disjointness and the point that would refute it.
-/
theorem Topology.exists_nbhd_disjoint_sUnion {X : Type u} (T : Topology X) {A : Set X}
    {G : Set (Set X)} (hfin : G.Finite)
    (h : ∀ V ∈ G, ∃ U, T.IsOpen U ∧ A ⊆ U ∧ U ∩ V = ∅) :
    ∃ U, T.IsOpen U ∧ A ⊆ U ∧ U ∩ ⋃₀ G = ∅ := by
  induction G, hfin using Set.Finite.induction_on with
  | empty => exact ⟨Set.univ, T.univ, Set.subset_univ A, by rw [Set.sUnion_empty, Set.inter_empty]⟩
  | insert _ _ ih =>
    obtain ⟨U, hUo, hAU, hUV⟩ := h _ (Set.mem_insert _ _)
    obtain ⟨W, hWo, hAW, hWG⟩ := ih (fun V hV => h V (Set.mem_insert_of_mem _ hV))
    refine ⟨U ∩ W, T.inter hUo hWo, Set.subset_inter hAU hAW, ?_⟩
    rw [Set.sUnion_insert]
    apply Set.eq_empty_of_forall_notMem
    rintro z ⟨⟨hzU, hzW⟩, hz⟩
    rcases hz with hz | hz
    · exact Set.eq_empty_iff_forall_notMem.mp hUV z ⟨hzU, hz⟩
    · exact Set.eq_empty_iff_forall_notMem.mp hWG z ⟨hzW, hz⟩

/--
@problem separate_compact
@title A Compact Set Separated by Neighbourhoods
@concept compact_in_hausdorff

@preamble
Let `K` be compact, and suppose `A` is separated from each single point of `K`: for every `y` of `K` there are disjoint open sets, one holding `A` and one holding `y`. Then `A` is separated from the whole of `K` at once.

Collect the open sets that hold a point of `K` and are missed by an open set around `A` — the ones that come with a partner, so that no partner has to be chosen afterwards. They cover `K`, so finitely many of them do. Their union is open and holds `K`, and the last problem intersects the finitely many partners into one open set around `A` that misses it.
@description
Prove `Topology.exists_separating_of_isCompactSet`. The cover to hand to the compactness of `K` is `{W | T.IsOpen W ∧ ∃ U, T.IsOpen U ∧ A ⊆ U ∧ U ∩ W = ∅}`, whose members carry their own partners, and `⋃₀ G` is the second of the two open sets asked for.
-/
theorem Topology.exists_separating_of_isCompactSet {X : Type u} (T : Topology X)
    {A K : Set X} (hK : T.IsCompactSet K)
    (h : ∀ y ∈ K, ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ A ⊆ U ∧ y ∈ V ∧ U ∩ V = ∅) :
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ A ⊆ U ∧ K ⊆ V ∧ U ∩ V = ∅ := by
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hK {W | T.IsOpen W ∧ ∃ U, T.IsOpen U ∧ A ⊆ U ∧ U ∩ W = ∅}
    (fun W hW => hW.1) (fun y hy => by
      obtain ⟨U, V, hU, hV, hAU, hyV, hUV⟩ := h y hy
      exact ⟨V, ⟨hV, U, hU, hAU, hUV⟩, hyV⟩)
  obtain ⟨U, hUo, hAU, hUG⟩ :=
    Topology.exists_nbhd_disjoint_sUnion T hGfin (fun W hW => (hGF hW).2)
  exact ⟨U, ⋃₀ G, hUo, T.sUnion (fun W hW => (hGF hW).1), hAU, hGcov, hUG⟩

/-!
@problem compact_closed_hausdorff
@title A Compact Set of a Hausdorff Space is Closed
@concept compact_in_hausdorff

@preamble
In a Hausdorff space distinct points are separated, so a point outside `K` is separated from each point of `K` in turn, and the last problem separates it from `K` entire.

That is already the closedness. The open set around the point misses the open set holding `K`, so it misses `K`, and every point outside `K` has an open set around it inside the complement — which is what it is for the complement to be open.

The same statement for a metric space was proved by taking the smallest of finitely many radii. Here there are no radii, and the intersection of finitely many open sets does that work.
@description
Prove `Topology.exists_separating_point`, which is the last problem at `A = {x}`, and then `Topology.isClosed_of_isCompactSet`. `Set.singleton_subset_iff` passes between `x ∈ U` and `{x} ⊆ U`; for the second, `Topology.isOpen_iff_nbhd` reduces openness of the complement to a neighbourhood at each of its points.
-/

theorem Topology.exists_separating_point {X : Type u} (T : Topology X)
    (hT : T.IsHausdorff) {K : Set X} (hK : T.IsCompactSet K) {x : X} (hx : x ∉ K) :
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ K ⊆ V ∧ U ∩ V = ∅ := by
  obtain ⟨U, V, hU, hV, hxU, hKV, hUV⟩ :=
    Topology.exists_separating_of_isCompactSet (A := {x}) T hK (fun y hy => by
      obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := hT x y (fun e => hx (e ▸ hy))
      exact ⟨U, V, hU, hV, Set.singleton_subset_iff.mpr hxU, hyV, hUV⟩)
  exact ⟨U, V, hU, hV, hxU rfl, hKV, hUV⟩

theorem Topology.isClosed_of_isCompactSet {X : Type u} (T : Topology X) (hT : T.IsHausdorff)
    {K : Set X} (hK : T.IsCompactSet K) : T.IsClosed K := by
  show T.IsOpen Kᶜ
  rw [Topology.isOpen_iff_nbhd T]
  intro x hx
  obtain ⟨U, V, hU, _, hxU, hKV, hUV⟩ :=
    Topology.exists_separating_point T hT hK hx
  exact ⟨U, hU, hxU, fun z hzU hzK => Set.eq_empty_iff_forall_notMem.mp hUV z ⟨hzU, hKV hzK⟩⟩

/-! @end -/

/--
@problem compact_iff_closed
@title Compact Means Closed, and Closed Compact
@concept compact_in_hausdorff

@preamble
A closed subset of a compact space is compact, and a compact subset of a Hausdorff space is closed. Where both hypotheses are in force the two implications meet: the compact subsets of a compact Hausdorff space are exactly its closed subsets.

Neither half is new. What is new is that they fit together, and from here on either word may be used for the other.
@description
Prove `Topology.isCompactSet_iff_isClosed` from the previous problem and the earlier `Topology.isCompactSet_of_isClosed`.
-/
theorem Topology.isCompactSet_iff_isClosed {X : Type u} (T : Topology X) (hX : T.IsCompact)
    (hT : T.IsHausdorff) (K : Set X) : T.IsCompactSet K ↔ T.IsClosed K :=
  ⟨fun h => Topology.isClosed_of_isCompactSet T hT h,
   fun h => Topology.isCompactSet_of_isClosed T hX h⟩

/-!
@concept compact_to_hausdorff
@title Maps Out of a Compact Space
@kind theorem

A continuous map is tested on preimages and says nothing of its own about images. A compact source and a Hausdorff target supply what is missing: such a map carries closed sets to closed sets, and a map that does that is a homeomorphism as soon as it is a bijection. It is the cheapest test for a homeomorphism the subject has.
-/

/--
@problem compact_closed_map
@title A Map From a Compact Space to a Hausdorff Space is Closed
@concept compact_to_hausdorff

@preamble
Let `f` be continuous, with a compact source and a Hausdorff target, and let `C` be closed in the source. Three facts already proved carry `C` to a closed set: a closed subset of a compact space is compact, the continuous image of a compact set is compact, and a compact set of a Hausdorff space is closed.

Nothing else is used, and nothing else is available — the target is not assumed compact, and the source is not assumed Hausdorff.
@description
Prove `Topology.isClosedMap_of_isCompact` by composing `Topology.isCompactSet_of_isClosed`, `Topology.isCompactSet_image` and `Topology.isClosed_of_isCompactSet`, in that order.
-/
theorem Topology.isClosedMap_of_isCompact {X : Type u} {Y : Type v} (T : Topology X)
    (T' : Topology Y) (hX : T.IsCompact) (hY : T'.IsHausdorff) {f : X → Y}
    (hf : T.Continuous T' f) : T.IsClosedMap T' f := fun _ hC =>
  Topology.isClosed_of_isCompactSet T' hY
    (Topology.isCompactSet_image T hf (Topology.isCompactSet_of_isClosed T hX hC))

/-!
@problem homeomorphism_of_closed_map
@title A Continuous Closed Bijection is a Homeomorphism
@concept compact_to_hausdorff

@preamble
A continuous bijection that is an open map is a homeomorphism; one that is a closed map is a homeomorphism too, for the same reason with a complement inserted. The preimage of an open `U` under the inverse is the image of `U` under the map, which is the complement of the image of `Uᶜ` — and the closed-map hypothesis calls that image closed.

With the last problem the hypothesis comes free. A continuous bijection from a compact space to a Hausdorff space is a homeomorphism, and no property of the inverse has to be checked at all.
@description
Define `Homeomorphism.ofClosedMap`, from a continuous closed `f` and a two-sided inverse `g`, and then `Homeomorphism.ofCompactToHausdorff`, which discharges the closed-map hypothesis by the last problem. As in `Homeomorphism.ofOpenMap`, the bijection is presented by the map that undoes it, and only `continuous_invFun` needs an argument: `image_eq_preimage_of_inverse`, with `Set.preimage_compl` and `compl_compl` around it.
-/

def Homeomorphism.ofClosedMap {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    {f : X → Y} {g : Y → X} (hf : T.Continuous T' f) (hclosed : T.IsClosedMap T' f)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) : Homeomorphism T T' where
  toFun := f
  invFun := g
  left_inv := hgf
  right_inv := hfg
  continuous_toFun := hf
  continuous_invFun := by
    intro U hU
    have hc : T.IsClosed Uᶜ := by
      show T.IsOpen _
      rw [compl_compl]
      exact hU
    have h : T'.IsOpen (f '' Uᶜ)ᶜ := hclosed Uᶜ hc
    rwa [image_eq_preimage_of_inverse hgf hfg Uᶜ, Set.preimage_compl, compl_compl] at h

def Homeomorphism.ofCompactToHausdorff {X : Type u} {Y : Type v} {T : Topology X}
    {T' : Topology Y} (hX : T.IsCompact) (hY : T'.IsHausdorff) {f : X → Y} {g : Y → X}
    (hf : T.Continuous T' f) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) :
    Homeomorphism T T' :=
  Homeomorphism.ofClosedMap hf (Topology.isClosedMap_of_isCompact T T' hX hY hf) hgf hfg

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (f : X → Y) (g : Y → X)
    (hX : T.IsCompact) (hY : T'.IsHausdorff) (hf : T.Continuous T' f)
    (hclosed : T.IsClosedMap T' f) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    (x : X) (y : Y) :
    (Homeomorphism.ofClosedMap hf hclosed hgf hfg).toFun x = f x
      ∧ (Homeomorphism.ofClosedMap hf hclosed hgf hfg).invFun y = g y
      ∧ (Homeomorphism.ofCompactToHausdorff hX hY hf hgf hfg).toFun x = f x
      ∧ (Homeomorphism.ofCompactToHausdorff hX hY hf hgf hfg).invFun y = g y :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! @end -/

/--
@problem compact_quotient
@title A Continuous Surjection Exhibits the Quotient Topology
@concept compact_to_hausdorff

@preamble
Let `f` be a continuous surjection from a compact space to a Hausdorff space. Then the target's topology is not merely coarse enough for `f` to be continuous: it is the finest topology that is, which is to say the one `f` coinduces.

One direction is the continuity. For the other, let the preimage of `U` be open. Then the preimage of `Uᶜ` is closed, its image is closed by the last problem but one, and that image is `Uᶜ` itself because `f` is onto — so `U` is open.

However the target's points were come by, they may as well have been glued together out of the source.
@description
Prove `Topology.eq_coinduced_of_isCompact`. `Topology.eq_of_isOpen_iff` reduces an equality of topologies to an equivalence at each set, and `Set.image_preimage_eq` is where the surjectivity is spent.
-/
theorem Topology.eq_coinduced_of_isCompact {X : Type u} {Y : Type v} (T : Topology X)
    (T' : Topology Y) (hX : T.IsCompact) (hY : T'.IsHausdorff) {f : X → Y}
    (hf : T.Continuous T' f) (hsurj : Function.Surjective f) : T' = T.coinduced f := by
  apply Topology.eq_of_isOpen_iff
  intro U
  refine ⟨fun hU => hf U hU, fun hU => ?_⟩
  have hc : T.IsClosed (f ⁻¹' Uᶜ) := by
    show T.IsOpen _
    rw [Set.preimage_compl, compl_compl]
    exact hU
  have h := Topology.isClosedMap_of_isCompact T T' hX hY hf _ hc
  rw [Set.image_preimage_eq _ hsurj] at h
  have h2 : T'.IsOpen Uᶜᶜ := h
  rwa [compl_compl] at h2

/-!
@concept compact_normal
@title Compact Hausdorff Spaces are Normal
@kind theorem

The axioms above Hausdorff ask that a point, and then a closed set, be held apart from a closed set, and no space has yet been shown to satisfy them but the discrete one and the metric ones. A compact Hausdorff space satisfies both, because in it a closed set is compact and a compact set behaves like a point.
-/

/--
@problem compact_regular
@title A Compact Hausdorff Space is Regular
@concept compact_normal

@preamble
Regularity asks that a point outside a closed set be held apart from it by disjoint open sets. In a compact space a closed set is compact, and a compact set of a Hausdorff space is held apart from every point outside it — which is that condition, word for word.

The T₁ half comes from the Hausdorff hypothesis, as it does everywhere in the hierarchy.
@description
Prove `Topology.isRegular_of_isCompact`. Its two halves are `Topology.isT1_of_isHausdorff` and `Topology.exists_separating_point` applied to `Topology.isCompactSet_of_isClosed`.
-/
theorem Topology.isRegular_of_isCompact {X : Type u} (T : Topology X) (hX : T.IsCompact)
    (hT : T.IsHausdorff) : T.IsRegular :=
  ⟨Topology.isT1_of_isHausdorff hT, fun _ _ hC hx =>
    Topology.exists_separating_point T hT
      (Topology.isCompactSet_of_isClosed T hX hC) hx⟩

/--
@problem compact_hausdorff_normal
@title A Compact Hausdorff Space is Normal
@concept compact_normal

@preamble
Normality asks the same of two disjoint closed sets, and both of them are compact, so the argument of this concept is run a second time.

By regularity, each point of the first closed set is held apart from the second: an open set around the point, an open set holding the second, and the two disjoint. The first set is compact, so the separation of a compact set from a set it is pointwise separated from applies with the roles exchanged, and returns the pair normality asked for.
@description
Prove `Topology.isNormal_of_isCompact`. The pointwise hypothesis to hand to `Topology.exists_separating_of_isCompactSet` is the last problem at each point of `C`, with `D` standing in the place of `A`; `Set.inter_comm` puts each disjointness the way round the side using it wants.
-/
theorem Topology.isNormal_of_isCompact {X : Type u} (T : Topology X) (hX : T.IsCompact)
    (hT : T.IsHausdorff) : T.IsNormal := by
  refine ⟨Topology.isT1_of_isHausdorff hT, fun C D hC hD hCD => ?_⟩
  have hsep : ∀ y ∈ C, ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ D ⊆ U ∧ y ∈ V ∧ U ∩ V = ∅ := by
    intro y hy
    obtain ⟨V, U, hV, hU, hyV, hDU, hVU⟩ :=
      (Topology.isRegular_of_isCompact T hX hT).2 y D hD
        (fun hyD => Set.eq_empty_iff_forall_notMem.mp hCD y ⟨hy, hyD⟩)
    exact ⟨U, V, hU, hV, hDU, hyV, by rw [Set.inter_comm]; exact hVU⟩
  obtain ⟨U, V, hU, hV, hDU, hCV, hUV⟩ :=
    Topology.exists_separating_of_isCompactSet T (Topology.isCompactSet_of_isClosed T hX hC) hsep
  exact ⟨V, U, hV, hU, hCV, hDU, by rw [Set.inter_comm]; exact hUV⟩

/-!
@concept tube_lemma
@title The Tube Lemma
@kind theorem

An open set of a product that holds one whole fibre holds a slab around it, provided the fibre is compact. It is the one thing compactness tells us about a product that openness alone does not, and the product of two compact spaces is compact because of it.
-/

/--
@problem box_union
@title A Box Over Finitely Many Sets
@concept tube_lemma

@preamble
Suppose that for each member `V` of a collection there is an open `U` around a point `x` with the box `U ×ˢ V` inside a given set `W`. For two members, the box over the union is handled by intersecting the two first sides: a point of `U ∩ U'` paired with a point of `V ∪ V'` lies in one of the two boxes already known to be inside `W`.

Finitely many are two at a time repeated. This is the second induction of that shape in the section: the first intersected open sets to miss a union, and this one intersects them to cover one.
@description
Prove `Topology.exists_box_sUnion`: for a finite `G`, one open `U` around `x` has `U ×ˢ ⋃₀ G ⊆ W`. `Set.prod_empty` handles the empty collection, whose union is empty, and `Set.sUnion_insert` the step; a membership `p ∈ U ×ˢ V` is the pair of `p.1 ∈ U` and `p.2 ∈ V`.
-/
theorem Topology.exists_box_sUnion {X : Type u} {Y : Type v} (T : Topology X) {x : X}
    {W : Set (X × Y)} {G : Set (Set Y)} (hfin : G.Finite)
    (h : ∀ V ∈ G, ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ×ˢ V ⊆ W) :
    ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ×ˢ ⋃₀ G ⊆ W := by
  induction G, hfin using Set.Finite.induction_on with
  | empty =>
    refine ⟨Set.univ, T.univ, trivial, ?_⟩
    rw [Set.sUnion_empty, Set.prod_empty]
    exact Set.empty_subset W
  | insert _ _ ih =>
    obtain ⟨U, hUo, hxU, hUV⟩ := h _ (Set.mem_insert _ _)
    obtain ⟨U', hU'o, hxU', hU'G⟩ := ih (fun V hV => h V (Set.mem_insert_of_mem _ hV))
    refine ⟨U ∩ U', T.inter hUo hU'o, ⟨hxU, hxU'⟩, ?_⟩
    rw [Set.sUnion_insert]
    rintro p ⟨hp1, hp2 | hp2⟩
    · exact hUV ⟨hp1.1, hp2⟩
    · exact hU'G ⟨hp1.2, hp2⟩

/--
@problem tube
@title The Tube Lemma
@concept tube_lemma

@preamble
Let `W` be open in a product and let it hold the fibre `{x} ×ˢ B` over a point `x`, with `B` compact. Around each point `(x, y)` of that fibre the definition of the product topology puts a box inside `W`, and the second sides of those boxes cover `B`.

By compactness finitely many of them do, and the last problem intersects their first sides into one open `U` around `x` with `U ×ˢ B` inside `W`. The fibre may be thickened to a slab, and the thickness does not depend on the point of `B`.

Compactness is what makes this true. Without it the widths could shrink towards zero along `B`, with no positive width below them all.
@description
Prove `Topology.tube_lemma`. The cover to hand to `B` is `{V | T'.IsOpen V ∧ ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ×ˢ V ⊆ W}`, each member carrying the first side it was found with — exactly as the cover in `separate_compact` carried its partner.
-/
theorem Topology.tube_lemma {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    {B : Set Y} (hB : T'.IsCompactSet B) {x : X} {W : Set (X × Y)}
    (hW : (T.prod T').IsOpen W) (hxW : {x} ×ˢ B ⊆ W) :
    ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ×ˢ B ⊆ W := by
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hB {V | T'.IsOpen V ∧ ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ×ˢ V ⊆ W}
    (fun V hV => hV.1) (fun y hy => by
      obtain ⟨U, V, hU, hV, hpUV, hsub⟩ := hW (x, y) (hxW ⟨rfl, hy⟩)
      exact ⟨V, ⟨hV, U, hU, hpUV.1, hsub⟩, hpUV.2⟩)
  obtain ⟨U, hUo, hxU, hsub⟩ := Topology.exists_box_sUnion T hGfin (fun V hV => (hGF hV).2)
  exact ⟨U, hUo, hxU, fun p hp => hsub ⟨hp.1, hGcov hp.2⟩⟩

/--
@problem slice_compact
@title A Fibre of a Product is Compact
@concept tube_lemma

@preamble
The fibre `{x} ×ˢ B` is the image of `B` under the map pairing a point of the second factor with the fixed `x`, and that map was shown continuous when the product was built. The continuous image of a compact set is compact, so the fibre is compact in the product — and the product topology is never opened up to see it.
@description
Prove `Topology.isCompactSet_slice`. `Topology.continuous_mk_right` is the map and `Topology.isCompactSet_image` carries the compactness across it; what remains is the set equality `(fun y => (x, y)) '' B = {x} ×ˢ B`, proved by `Set.ext` at a point `p` and rebuilt from `p.1` and `p.2`.
-/
theorem Topology.isCompactSet_slice {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    {B : Set Y} (hB : T'.IsCompactSet B) (x : X) : (T.prod T').IsCompactSet ({x} ×ˢ B) := by
  have hc := Topology.isCompactSet_image T' (Topology.continuous_mk_right T T' x) hB
  have he : (fun y => (x, y)) '' B = {x} ×ˢ B := by
    apply Set.ext
    intro p
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨rfl, hy⟩
    · rintro ⟨h1, h2⟩
      have e : p.1 = x := h1
      exact ⟨p.2, h2, by rw [← e]⟩
  rwa [he] at hc

/--
@problem patchwork
@title Finitely Many Finite Subcovers
@concept tube_lemma

@preamble
Let each member `U` of a finite collection of sets of the first factor come with a finite piece of a cover doing for the slab `U ×ˢ B` above it. Uniting two finite pieces leaves a finite piece, and it does for the slab above the union of the two sets.

That is the whole of the step, and this is the third induction on a finite set in the section, and the last.
@description
Prove `Topology.exists_finite_subcover_sUnion`: given a finite `G`, each of whose members `U` has a finite `H ⊆ F` with `U ×ˢ B ⊆ ⋃₀ H`, there is one finite `H ⊆ F` with `(⋃₀ G) ×ˢ B ⊆ ⋃₀ H`. `Set.empty_prod` handles the empty collection, `Set.Finite.union` the step, and `Set.sUnion_mono` carries a point of one piece into the union of both.
-/
theorem Topology.exists_finite_subcover_sUnion {X : Type u} {Y : Type v} {F : Set (Set (X × Y))}
    {B : Set Y} {G : Set (Set X)} (hfin : G.Finite)
    (h : ∀ U ∈ G, ∃ H ⊆ F, H.Finite ∧ U ×ˢ B ⊆ ⋃₀ H) :
    ∃ H ⊆ F, H.Finite ∧ (⋃₀ G) ×ˢ B ⊆ ⋃₀ H := by
  induction G, hfin using Set.Finite.induction_on with
  | empty =>
    refine ⟨∅, Set.empty_subset F, Set.finite_empty, ?_⟩
    rw [Set.sUnion_empty, Set.empty_prod]
    exact Set.empty_subset _
  | insert _ _ ih =>
    obtain ⟨H, hHF, hHfin, hHsub⟩ := h _ (Set.mem_insert _ _)
    obtain ⟨H', hH'F, hH'fin, hH'sub⟩ := ih (fun U hU => h U (Set.mem_insert_of_mem _ hU))
    refine ⟨H ∪ H', Set.union_subset hHF hH'F, hHfin.union hH'fin, ?_⟩
    rw [Set.sUnion_insert]
    rintro p ⟨hp1 | hp1, hp2⟩
    · exact Set.sUnion_mono Set.subset_union_left (hHsub ⟨hp1, hp2⟩)
    · exact Set.sUnion_mono Set.subset_union_right (hH'sub ⟨hp1, hp2⟩)

/-!
@problem product_compact
@title The Product of Two Compact Sets
@concept tube_lemma

@preamble
Let `A` and `B` be compact and let `F` cover `A ×ˢ B`. Fix a point `x` of `A`. The fibre above it is compact, so finitely many members of `F` cover that fibre; their union is open and holds it, so the tube lemma returns an open `U` around `x` with the whole slab `U ×ˢ B` inside that union.

The sets `U` so obtained cover `A`, each carrying the finite piece of `F` that serves its slab. Finitely many of them cover `A`, and uniting their pieces gives one finite subcollection covering `A ×ˢ B`.

The statement about spaces is the case `A = B = Set.univ`, a product of two whole sets being the whole product.
@description
Prove `Topology.isCompactSet_prod` and then `Topology.isCompact_prod`. The cover of `A` is `{U | T.IsOpen U ∧ ∃ H ⊆ F, H.Finite ∧ U ×ˢ B ⊆ ⋃₀ H}`, each member carrying its own finite piece, and `Set.univ_prod_univ` reads the second theorem off the first.
-/

theorem Topology.isCompactSet_prod {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    {A : Set X} {B : Set Y} (hA : T.IsCompactSet A) (hB : T'.IsCompactSet B) :
    (T.prod T').IsCompactSet (A ×ˢ B) := by
  intro F hFo hFcov
  obtain ⟨G, hGF, hGfin, hGcov⟩ :=
    hA {U | T.IsOpen U ∧ ∃ H ⊆ F, H.Finite ∧ U ×ˢ B ⊆ ⋃₀ H} (fun U hU => hU.1) (fun x hx => by
      obtain ⟨H, hHF, hHfin, hHcov⟩ := Topology.isCompactSet_slice T T' hB x F hFo
        (fun p hp => hFcov ⟨by rw [show p.1 = x from hp.1]; exact hx, hp.2⟩)
      obtain ⟨U, hUo, hxU, hUsub⟩ := Topology.tube_lemma T T' hB
        ((T.prod T').sUnion (fun V hV => hFo V (hHF hV))) hHcov
      exact ⟨U, ⟨hUo, H, hHF, hHfin, hUsub⟩, hxU⟩)
  obtain ⟨H, hHF, hHfin, hHsub⟩ :=
    Topology.exists_finite_subcover_sUnion hGfin (fun U hU => (hGF hU).2)
  exact ⟨H, hHF, hHfin, fun p hp => hHsub ⟨hGcov hp.1, hp.2⟩⟩

theorem Topology.isCompact_prod {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y)
    (hX : T.IsCompact) (hY : T'.IsCompact) : (T.prod T').IsCompact := by
  have h := Topology.isCompactSet_prod T T' hX hY
  rwa [Set.univ_prod_univ] at h

/-! @end -/

/-!
@concept heine_borel
@title The Heine-Borel Theorem
@kind theorem
@goal

Which sets of the line are compact? The last section proved half an answer — a compact set is closed and bounded — and the unit interval supplies the other half. The theorem that results is the one calculus quotes without proving, and the same argument settles the plane, once the plane is known to be a product of two lines.
-/

/--
@problem closed_in_compact
@title A Closed Subset of a Compact Set
@concept heine_borel

@preamble
A closed subset of a compact space is compact, and the proof of that never used that the ambient set was the whole space. Throw the complement of the closed set in with the cover, keep the finitely many that come back, and throw the complement away again.

Stated of a compact set rather than a compact space, the same argument gives what this concept needs: a set is compact as soon as it is closed and lies inside something compact.
@description
Prove `Topology.isCompactSet_of_isClosed_subset`, which is the earlier `Topology.isCompactSet_of_isClosed` with `Set.univ` replaced by a compact `K`. `insert Cᶜ F` is the enlarged cover, `G ∩ F` the collection with `Cᶜ` thrown away, and `Or.resolve_left` rules out the discarded member at a point of `C`.
-/
theorem Topology.isCompactSet_of_isClosed_subset {X : Type u} (T : Topology X) {K : Set X}
    (hK : T.IsCompactSet K) {C : Set X} (hC : T.IsClosed C) (hCK : C ⊆ K) :
    T.IsCompactSet C := by
  intro F hFo hcov
  have hopen : ∀ U ∈ insert Cᶜ F, T.IsOpen U := by
    rintro U (rfl | hU)
    exacts [hC, hFo U hU]
  have hKcov : K ⊆ ⋃₀ insert Cᶜ F := by
    intro x _
    by_cases hxC : x ∈ C
    · obtain ⟨U, hUF, hxU⟩ := hcov hxC
      exact ⟨U, Set.mem_insert_of_mem _ hUF, hxU⟩
    · exact ⟨Cᶜ, Set.mem_insert _ _, hxC⟩
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hK _ hopen hKcov
  refine ⟨G ∩ F, Set.inter_subset_right, hGfin.subset Set.inter_subset_left, fun x hx => ?_⟩
  obtain ⟨U, hUG, hxU⟩ := hGcov (hCK hx)
  exact ⟨U, ⟨hUG, (hGF hUG).resolve_left (fun e => (e ▸ hxU) hx)⟩, hxU⟩

/-!
@problem segment_compact
@title Every Closed Interval is Compact
@concept heine_borel

@preamble
The unit interval is compact, and so is every closed interval, because an interval is an affine copy of the unit one. The map `t ↦ (b - a) * t + a` carries `0` to `a` and `1` to `b`, and when `a < b` it carries the unit interval onto the interval from `a` to `b` exactly — the point landing on `x` being `(x - a) / (b - a)`. It is continuous, and the continuous image of a compact set is compact.

The degenerate case is separate: when `a = b` the interval is a single point, compact for the reason any finite set is.
@description
Prove `line_image_unitInterval`, the image of the unit interval under that map, and then `line_isCompactSet_segment`. For the first, `nlinarith` handles the two products in one direction and `div_le_one` the quotient in the other, with `field_simp` and `ring` for the point that lands on `x`. For the second, `eq_or_lt_of_le` splits the hypothesis and `line_continuous_affine_top` supplies the continuity.
-/

theorem line_image_unitInterval {a b : ℝ} (hlt : a < b) :
    (fun t => (b - a) * t + a) '' unitInterval = {x | a ≤ x ∧ x ≤ b} := by
  have hne : b - a ≠ 0 := by linarith
  apply Set.ext
  rintro x
  refine ⟨?_, fun hx => ⟨(x - a) / (b - a), ⟨?_, ?_⟩, ?_⟩⟩
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · exact div_nonneg (by linarith [hx.1]) (by linarith)
  · rw [div_le_one (by linarith)]; linarith [hx.2]
  · field_simp
    ring

theorem line_isCompactSet_segment {a b : ℝ} (hab : a ≤ b) :
    line.toTopology.IsCompactSet {x | a ≤ x ∧ x ≤ b} := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have e : {x : ℝ | a ≤ x ∧ x ≤ a} = {a} :=
      Set.ext (fun x => ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩)
    rw [e]
    exact Topology.isCompactSet_singleton line.toTopology a
  · rw [← line_image_unitInterval hlt]
    exact Topology.isCompactSet_image line.toTopology
      (line_continuous_affine_top (b - a) a (by linarith)) unitInterval_isCompactSet

/-! @end -/

/--
@problem heine_borel_line
@title The Heine-Borel Theorem on the Line
@concept heine_borel

@preamble
A set of real numbers is compact exactly when it is closed and bounded.

One direction is the last section's: a compact set of a metric space is bounded, and — the line being a metric space — closed. The other is the two problems above. A bounded set lies inside a closed interval, a closed interval is compact, and a closed subset of a compact set is compact.

The empty set is looked at separately in the first direction, since boundedness names a centre and the argument that produces one wants a point of the set to start from.
@description
Prove `line_isCompactSet_iff`. `Set.eq_empty_or_nonempty` splits off the empty case in each direction; the interval to use is the one from `x - ε` to `x + ε`, and `abs_lt` turns a membership in the ball into the two inequalities that put a point of the set inside it.
-/
theorem line_isCompactSet_iff {K : Set ℝ} :
    line.toTopology.IsCompactSet K ↔ line.toTopology.IsClosed K ∧ line.IsBounded K := by
  refine ⟨fun hK => ⟨Metric.isClosed_of_isCompactSet line hK, ?_⟩, ?_⟩
  · rcases Set.eq_empty_or_nonempty K with rfl | hne
    · exact ⟨0, 0, Set.empty_subset _⟩
    · exact Metric.isBounded_of_isCompactSet line hK hne
  · rintro ⟨hC, hB⟩
    rcases Set.eq_empty_or_nonempty K with rfl | ⟨y, hy⟩
    · exact Topology.isCompactSet_empty line.toTopology
    obtain ⟨x, ε, hsub⟩ := hB
    have hy' : |x - y| < ε := hsub hy
    refine Topology.isCompactSet_of_isClosed_subset line.toTopology
      (line_isCompactSet_segment (show x - ε ≤ x + ε by linarith [abs_nonneg (x - y)]))
      hC (fun z hz => ?_)
    have hz' : |x - z| < ε := hsub hz
    rw [abs_lt] at hz'
    exact ⟨by linarith [hz'.2], by linarith [hz'.1]⟩

/-!
@problem plane_boxes
@title Closed Boxes of the Plane
@concept heine_borel

@preamble
The supremum plane and the product of two lines call the same sets open. They are therefore not merely homeomorphic but equal as topologies, and a statement proved of one is a statement about the other with no map standing in between.

A supremum ball is a square, so it lies inside the closed box of the same radius about the same centre; and a closed box is a product of two closed intervals, which the last concept and the last problem make compact.
@description
Prove `supNorm_toTopology_eq_prod` from `Topology.eq_of_isOpen_iff` and the two implications proved when the plane was identified with a product. Then `supNorm_ball_subset_box`, where `max_lt_iff` and `abs_lt` restate a membership in a supremum ball as four inequalities. Then `supNorm_isCompactSet_box`, which rewrites by the first and applies `Topology.isCompactSet_prod`.
-/

theorem supNorm_toTopology_eq_prod :
    supNorm.toMetric.toTopology = line.toTopology.prod line.toTopology :=
  Topology.eq_of_isOpen_iff
    (fun _ => ⟨isOpen_prod_of_isOpenSet_supNorm, isOpenSet_supNorm_of_isOpen_prod⟩)

theorem supNorm_ball_subset_box (p : ℝ × ℝ) (ε : ℝ) :
    supNorm.toMetric.ball p ε ⊆
      {x | p.1 - ε ≤ x ∧ x ≤ p.1 + ε} ×ˢ {y | p.2 - ε ≤ y ∧ y ≤ p.2 + ε} := by
  intro z hz
  have hz' : max |p.1 - z.1| |p.2 - z.2| < ε := hz
  rw [max_lt_iff, abs_lt, abs_lt] at hz'
  exact ⟨⟨by linarith [hz'.1.2], by linarith [hz'.1.1]⟩,
    ⟨by linarith [hz'.2.2], by linarith [hz'.2.1]⟩⟩

theorem supNorm_isCompactSet_box (p : ℝ × ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    supNorm.toMetric.toTopology.IsCompactSet
      ({x | p.1 - ε ≤ x ∧ x ≤ p.1 + ε} ×ˢ {y | p.2 - ε ≤ y ∧ y ≤ p.2 + ε}) := by
  rw [supNorm_toTopology_eq_prod]
  exact Topology.isCompactSet_prod line.toTopology line.toTopology
    (line_isCompactSet_segment (by linarith)) (line_isCompactSet_segment (by linarith))

/-! @end -/

/--
@problem heine_borel_plane
@title The Heine-Borel Theorem in the Plane
@concept heine_borel

@preamble
The plane goes the way the line went, with a box in place of an interval. A compact set is closed and bounded because the plane is a metric space; a closed and bounded set lies inside a closed box, a box is compact, and a closed subset of a compact set is compact.

The plane measured by the taxicab length gives the same answer, being the same space. The plane measured by the Euclidean length is not settled here, since its norm needs a square root and this subject has none.
@description
Prove `supNorm_isCompactSet_iff`. The two directions are those of `line_isCompactSet_iff`, with `supNorm_isCompactSet_box` in place of the interval and `supNorm_ball_subset_box` for the containment; the radius is non-negative because a point of the set is nearer to the centre than it.
-/
theorem supNorm_isCompactSet_iff {S : Set (ℝ × ℝ)} :
    supNorm.toMetric.toTopology.IsCompactSet S ↔
      supNorm.toMetric.toTopology.IsClosed S ∧ supNorm.toMetric.IsBounded S := by
  refine ⟨fun hS => ⟨Metric.isClosed_of_isCompactSet supNorm.toMetric hS, ?_⟩, ?_⟩
  · rcases Set.eq_empty_or_nonempty S with rfl | hne
    · exact ⟨(0, 0), 0, Set.empty_subset _⟩
    · exact Metric.isBounded_of_isCompactSet supNorm.toMetric hS hne
  · rintro ⟨hC, hB⟩
    rcases Set.eq_empty_or_nonempty S with rfl | ⟨q, hq⟩
    · exact Topology.isCompactSet_empty supNorm.toMetric.toTopology
    obtain ⟨p, ε, hsub⟩ := hB
    have hq' : max |p.1 - q.1| |p.2 - q.2| < ε := hsub hq
    have hε : (0 : ℝ) ≤ ε :=
      le_of_lt (lt_of_le_of_lt (le_trans (abs_nonneg _) (le_max_left _ _)) hq')
    exact Topology.isCompactSet_of_isClosed_subset supNorm.toMetric.toTopology
      (supNorm_isCompactSet_box p hε) hC (fun z hz => supNorm_ball_subset_box p ε (hsub hz))

end GeneralTopology
