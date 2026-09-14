import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Sequences

/-! @section Compactness -/

universe u v

namespace GeneralTopology

/-!
@concept open_cover
@title Open Covers and Compact Sets
@kind definition

Spread open sets over a space until they cover it and you may need infinitely many of them. A set is compact when finitely many always suffice — when no open cover of it is irreducibly infinite. The condition looks like bookkeeping and is not: it is what a closed interval has and the whole line has not, and it is the reason so many theorems of analysis ask for a closed interval.
-/

/-!
@problem define_compact
@title Open Covers, Subcovers, and Compactness
@concept open_cover

@preamble
An *open cover* of a set `S` is a collection `F` of open sets whose union contains `S`, so that every point of `S` lies in at least one member. A collection of sets is a `Set (Set X)` and its union is `⋃₀ F`, as they were when the union condition of a topology was written down.

A *subcover* is a subcollection that still covers `S`. Compactness asks whether a finite one can always be found. Mathlib defines compactness by filters rather than covers, and recovers this form as `isCompact_iff_finite_subcover`.

We ask the question of a set, using the open sets of the space around it, and read it off at the whole space to ask it of the space. `S.Finite` says that `S` has finitely many points, and `∃ G ⊆ F, p G` abbreviates `∃ G, G ⊆ F ∧ p G`.
@description
Define `TopologicalSpace.IsCompact T S`: for every `F : Set (Set X)` whose members are all open, if `S ⊆ ⋃₀ F` then some `G ⊆ F` has `G.Finite` and `S ⊆ ⋃₀ G`, those two conjuncts in that order. Then define `TopologicalSpace.IsCompactSpace` as `T.IsCompact Set.univ`. Both containments are written `⊆`, not as equations.
-/

def TopologicalSpace.IsCompact {X : Type u} (T : TopologicalSpace X) (S : Set X) : Prop :=
  ∀ F : Set (Set X), (∀ U ∈ F, T.IsOpen U) → S ⊆ ⋃₀ F →
    ∃ G ⊆ F, G.Finite ∧ S ⊆ ⋃₀ G

def TopologicalSpace.IsCompactSpace {X : Type u} (T : TopologicalSpace X) : Prop
    := T.IsCompact Set.univ

/-- @spec -/
example (X : Type) (T : TopologicalSpace X) (S : Set X) :
    (T.IsCompact S ↔ ∀ F : Set (Set X), (∀ U ∈ F, T.IsOpen U) → S ⊆ ⋃₀ F →
        ∃ G ⊆ F, G.Finite ∧ S ⊆ ⋃₀ G)
      ∧ (T.IsCompactSpace ↔ T.IsCompact Set.univ) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! @end -/

/-!
@problem compact_small
@title The Empty Set and a Single Point
@concept open_cover

@preamble
Two sets are compact because there is so little of them to cover. The empty set needs no member of the cover at all, so the empty subcollection serves, and it is finite because it has no members.

A single point needs one. The cover reaches `x`, so some member `U` holds it; `{U}` is a subcollection of one set, and every point of `{x}` — which is to say `x` — lies in it.
@description
Prove `TopologicalSpace.isCompact_empty` and `TopologicalSpace.isCompact_singleton`. `Set.empty_subset` proves both obligations of the first. For the second, a membership `y ∈ {x}` is the equation `y = x` and must be named as one before it can be rewritten; `Set.singleton_subset_iff` turns a containment of a singleton into a membership.
-/

theorem TopologicalSpace.isCompact_empty {X : Type u} (T : TopologicalSpace X) :
    T.IsCompact (∅ : Set X) :=
  fun _ _ _ => ⟨∅, Set.empty_subset _, Set.finite_empty, Set.empty_subset _⟩

theorem TopologicalSpace.isCompact_singleton {X : Type u} (T : TopologicalSpace X) (x : X) :
    T.IsCompact {x} := by
  intro F _ hcov
  obtain ⟨U, hUF, hxU⟩ := hcov rfl
  refine ⟨{U}, Set.singleton_subset_iff.mpr hUF, Set.finite_singleton U, ?_⟩
  intro y hy
  have e : y = x := hy
  exact ⟨U, rfl, e ▸ hxU⟩

/-! @end -/

/--
@problem compact_union
@title A Union of Two Compact Sets
@concept open_cover

@preamble
A cover of `S ∪ S'` covers each half. Each half keeps finitely many members of it, and the two selections together are finitely many members covering the whole.

This is where *two* matters. Two finite selections have a finite union, and infinitely many of them need not; a union of infinitely many compact sets is usually not compact, the line being a union of closed intervals.
@description
Prove `TopologicalSpace.isCompact_union`. Feed each half its own restriction of the cover, then offer the union of the two subcollections; `Set.union_subset` shows it inside `F`, and `Set.Finite.union` that it is finite. `Set.sUnion_mono` carries a point of one subcollection's union into the union of both.
-/
theorem TopologicalSpace.isCompact_union {X : Type u} (T : TopologicalSpace X) {S S' : Set X}
    (hS : T.IsCompact S) (hS' : T.IsCompact S') : T.IsCompact (S ∪ S') := by
  intro F hFo hcov
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hS F hFo (fun x hx => hcov (Or.inl hx))
  obtain ⟨G', hG'F, hG'fin, hG'cov⟩ := hS' F hFo (fun x hx => hcov (Or.inr hx))
  refine ⟨G ∪ G', Set.union_subset hGF hG'F, hGfin.union hG'fin, ?_⟩
  rintro x (hx | hx)
  · exact Set.sUnion_mono Set.subset_union_left (hGcov hx)
  · exact Set.sUnion_mono Set.subset_union_right (hG'cov hx)

/-!
@concept compact_basics
@title What is Compact, and What is Not
@kind theorem

A definition earns its place by what it admits and what it rules out. Finitely many points are always compact, whatever topology they carry; of the two extreme topologies one is compact on every set and the other only on the finite ones. And compactness, once had, passes to the closed subsets — which is how most compact sets are come by.
-/

/-!
@problem compact_finite
@title A Finite Set is Compact
@concept compact_basics

@preamble
A set with finitely many points is compact, and no property of the topology is used: keep one member of the cover for each point and finitely many are kept.

The argument is an induction on the finiteness itself. A finite set is built from the empty set by adding one point at a time, so it is enough to know that the empty set is compact and that adding a point preserves compactness — and adding a point is uniting with a singleton, which the last problem already handles.
@description
Prove `TopologicalSpace.isCompact_of_finite` and then `TopologicalSpace.isCompactSpace_of_finite`, which is the first at `Set.univ`. `induction S, hS using Set.Finite.induction_on` splits the finiteness into its two cases, named `empty` and `insert`; `Set.insert_eq` rewrites `insert x S` as `{x} ∪ S`.
-/

theorem TopologicalSpace.isCompact_of_finite {X : Type u} (T : TopologicalSpace X) {S : Set X}
    (hS : S.Finite) : T.IsCompact S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact TopologicalSpace.isCompact_empty T
  | insert _ _ ih =>
    rw [Set.insert_eq]
    exact TopologicalSpace.isCompact_union T (TopologicalSpace.isCompact_singleton T _) ih

theorem TopologicalSpace.isCompactSpace_of_finite {X : Type u} (T : TopologicalSpace X)
    (h : (Set.univ : Set X).Finite) : T.IsCompactSpace :=
  TopologicalSpace.isCompact_of_finite T h

/-! @end -/

/-!
@problem compact_extremes
@title The Two Extremes
@concept compact_basics

@preamble
The indiscrete topology has two open sets, and a cover can only use them. Whichever member of a cover catches a point must be the whole space, since the empty set catches nothing, and that one member covers everything by itself. Every indiscrete space is compact, however many points it has.

The discrete topology is the other extreme, and it is the subject's first space that is not compact. Every singleton is open, so the singletons cover the space; and no finite collection of them covers a space with infinitely many points, since a finite union of finite sets is finite.
@description
Prove `indiscrete_isCompactSpace` and `discrete_not_isCompactSpace`. For the first, keep exactly the members equal to `Set.univ`, a subcollection of `{Set.univ}` and so finite. For the second, `Set.infinite_univ` is the contradiction wanted, `Set.Finite.sUnion` makes the union of a finite collection of finite sets finite, and `trivial` proves whatever the discrete topology asks.
-/

theorem indiscrete_isCompactSpace (X : Type u) : (indiscrete X).IsCompactSpace := by
  intro F hFo hcov
  refine ⟨{U | U ∈ F ∧ U = Set.univ}, fun U hU => hU.1,
    Set.Finite.subset (Set.finite_singleton Set.univ) (fun U hU => hU.2), ?_⟩
  intro y _
  obtain ⟨U, hUF, hyU⟩ := hcov (Set.mem_univ y)
  rcases hFo U hUF with h | h
  · rw [h] at hyU
    exact hyU.elim
  · exact ⟨U, ⟨hUF, h⟩, hyU⟩

theorem discrete_not_isCompactSpace (X : Type u) [Infinite X] : ¬ (discrete X).IsCompactSpace := by
  intro h
  obtain ⟨G, hGF, hGfin, hGcov⟩ := h {U | ∃ x : X, U = {x}} (fun _ _ => trivial)
    (fun x _ => ⟨{x}, ⟨x, rfl⟩, rfl⟩)
  refine Set.infinite_univ (α := X) (Set.Finite.subset ?_ hGcov)
  refine hGfin.sUnion ?_
  rintro U hU
  obtain ⟨x, rfl⟩ := hGF hU
  exact Set.finite_singleton x

/-! @end -/

/--
@problem compact_closed_subset
@title A Closed Subset of a Compact Space
@concept compact_basics

@preamble
Let `C` be closed in a compact space and let `F` cover `C`. Then `F` need not cover the space, but adding the one open set `Cᶜ` to it does: a point outside `C` is caught by `Cᶜ`, and a point inside it by a member of `F`.

The space is compact, so finitely many of those cover it. Throw `Cᶜ` away again. What is left is a finite subcollection of `F`, and it still covers `C`, because the member that caught a point of `C` was not the one thrown away.
@description
Prove `TopologicalSpace.isCompact_of_isClosed`. `insert Cᶜ F` is the enlarged cover, and `rintro U (rfl | hU)` splits a member of it into the new set and an old one. `G ∩ F` is the collection with `Cᶜ` thrown away; `Set.Finite.subset` shows it finite, and `Or.resolve_left` rules out the discarded member at a point of `C`.
-/
theorem TopologicalSpace.isCompact_of_isClosed {X : Type u} (T : TopologicalSpace X)
    (hT : T.IsCompactSpace)
    {C : Set X} (hC : T.IsClosed C) : T.IsCompact C := by
  intro F hFo hcov
  have hopen : ∀ U ∈ insert Cᶜ F, T.IsOpen U := by
    rintro U (rfl | hU)
    exacts [hC, hFo U hU]
  have huniv : (Set.univ : Set X) ⊆ ⋃₀ insert Cᶜ F := by
    intro x _
    by_cases hxC : x ∈ C
    · obtain ⟨U, hUF, hxU⟩ := hcov hxC
      exact ⟨U, Set.mem_insert_of_mem _ hUF, hxU⟩
    · exact ⟨Cᶜ, Set.mem_insert _ _, hxC⟩
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hT _ hopen huniv
  refine ⟨G ∩ F, Set.inter_subset_right, hGfin.subset Set.inter_subset_left, fun x hx => ?_⟩
  obtain ⟨U, hUG, hxU⟩ := hGcov (Set.mem_univ x)
  exact ⟨U, ⟨hUG, (hGF hUG).resolve_left (fun e => (e ▸ hxU) hx)⟩, hxU⟩

/-!
@concept compact_metric
@title Compact Sets in a Metric Space
@kind theorem

Where there are distances, a compact set cannot get away. It fits inside a single ball, and it holds every point it approaches. Each is proved the same way — cover the set with balls, keep finitely many, and take the largest or the smallest of the finitely many radii — and together they say what a compact set of real numbers looks like.
-/

/--
@problem bounded_sunion
@title A Finite Union of Bounded Sets
@concept compact_metric

@preamble
Two bounded sets have a ball holding both, and that is as far as the earlier argument went. Finitely many are two at a time repeated: add one set to the union and enlarge the ball once more.

The induction begins at the empty collection, whose union is empty and is held by a ball of radius zero — about any point at all. A point has to be supplied, since a space with no points has no balls, and here the point is an argument to the theorem.
@description
Prove `MetricSpace.isBounded_sUnion`: a finite collection of bounded sets has a bounded union, given a point `x₀` to centre the empty case on. `induction G, hfin using Set.Finite.induction_on` splits the finiteness, and `Set.sUnion_insert` rewrites the union of an enlarged collection as one set united with the rest.
-/
theorem MetricSpace.isBounded_sUnion {X : Type u} (M : MetricSpace X) (x₀ : X) {G : Set (Set X)}
    (hfin : G.Finite) (h : ∀ U ∈ G, M.IsBounded U) : M.IsBounded (⋃₀ G) := by
  induction G, hfin using Set.Finite.induction_on with
  | empty => exact ⟨x₀, 0, by rintro z ⟨U, hU, -⟩; exact hU.elim⟩
  | insert _ _ ih =>
    rw [Set.sUnion_insert]
    exact MetricSpace.isBounded_union M _ _ (h _ (Set.mem_insert _ _))
      (ih (fun U hU => h U (Set.mem_insert_of_mem _ hU)))

/-!
@problem compact_bounded
@title A Compact Set is Bounded
@concept compact_metric

@preamble
Cover a set by the balls of radius one about every point of the space. Every point is in the ball about itself, so this is a cover; if the set is compact, finitely many of those balls hold it, and a finite union of balls is bounded.

The set must be nonempty for the statement to mean anything, since boundedness names a centre and an empty space has no point to name.

The line is not compact, and boundedness is what says so. No ball holds the whole line: whatever centre and radius are offered, the point one radius to the right of the centre escapes.
@description
Prove `MetricSpace.isBounded_of_isCompact` and `line_not_isCompactSpace`. The cover is `{U | ∃ y : X, U = MetricSpace.ball M y 1}`; `MetricSpace.isOpenSet_ball` makes its members open and `MetricSpace.mem_ball_self` puts each point in one. For the line, apply the first to `Set.univ` and evaluate the distance that results.
-/

theorem MetricSpace.isBounded_of_isCompact {X : Type u} (M : MetricSpace X) {K : Set X}
    (hK : M.toTopologicalSpace.IsCompact K) (hne : K.Nonempty) : M.IsBounded K := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hK {U | ∃ y : X, U = MetricSpace.ball M y 1}
    (by rintro U ⟨y, rfl⟩; exact MetricSpace.isOpenSet_ball M y 1)
    (fun y _ => ⟨MetricSpace.ball M y 1, ⟨y, rfl⟩, MetricSpace.mem_ball_self M y 1 one_pos⟩)
  refine MetricSpace.isBounded_subset M _ _ (MetricSpace.isBounded_sUnion M x₀ hGfin ?_) hGcov
  rintro U hU
  obtain ⟨y, rfl⟩ := hGF hU
  exact MetricSpace.isBounded_ball M y 1

theorem line_not_isCompactSpace : ¬ line.toTopologicalSpace.IsCompactSpace := by
  intro h
  obtain ⟨x, ε, hsub⟩ := MetricSpace.isBounded_of_isCompact line h ⟨0, trivial⟩
  have h1 : |x - (x + ε)| < ε := hsub (Set.mem_univ _)
  have h2 : |x - (x + ε)| = |ε| := by ring_nf; rw [abs_neg]
  rw [h2] at h1
  exact absurd (le_abs_self ε) (not_le.mpr h1)

/-! @end -/

/-!
@problem keeping_distance
@title Balls That Keep Their Distance
@concept compact_metric

@preamble
Fix a point `x` and take any other point `y`. The ball about `y` of radius half the distance from `x` to `y` stays away from `x`: a point `z` of it satisfies `d(x, y) ≤ d(x, z) + d(z, y)` with `d(z, y)` less than half of `d(x, y)`, so `d(x, z)` is at least the other half.

That is one ball. For finitely many sets, each keeping some positive distance from `x`, the smallest of the distances is positive and every one of them keeps it — which is the second place in this section where finiteness is what makes a largest or a smallest exist.
@description
Prove `MetricSpace.half_dist_pos`, `MetricSpace.le_dist_of_mem_ball_half` and `MetricSpace.exists_dist_ge_sUnion`. `MetricSpace.dist_pos` from the section on separation is the positive distance between distinct points; restating a membership in a ball as the inequality it abbreviates, together with `MetricSpace.dist_triangle` and `MetricSpace.dist_comm`, gives the second to `linarith`. The third is again an induction on the finiteness, with `min` for the step.
-/

theorem MetricSpace.half_dist_pos {X : Type u} (M : MetricSpace X) {x y : X} (h : x ≠ y) :
    0 < M.dist x y / 2 := by
  have := MetricSpace.dist_pos M h
  linarith

theorem MetricSpace.le_dist_of_mem_ball_half {X : Type u} (M : MetricSpace X) {x y z : X}
    (h : z ∈ M.ball y (M.dist x y / 2)) : M.dist x y / 2 ≤ M.dist x z := by
  have h1 : M.dist y z < M.dist x y / 2 := h
  have h2 := M.dist_triangle x z y
  have h3 : M.dist z y = M.dist y z := M.dist_comm
  linarith

theorem MetricSpace.exists_dist_ge_sUnion {X : Type u} (M : MetricSpace X) {x : X} {G : Set (Set X)}
    (hfin : G.Finite) (h : ∀ U ∈ G, ∃ r > 0, ∀ z ∈ U, r ≤ M.dist x z) :
    ∃ r > 0, ∀ z ∈ ⋃₀ G, r ≤ M.dist x z := by
  induction G, hfin using Set.Finite.induction_on with
  | empty => exact ⟨1, one_pos, by rintro z ⟨U, hU, -⟩; exact hU.elim⟩
  | insert _ _ ih =>
    obtain ⟨r, hr, hrU⟩ := h _ (Set.mem_insert _ _)
    obtain ⟨s, hs, hsG⟩ := ih (fun U hU => h U (Set.mem_insert_of_mem _ hU))
    refine ⟨min r s, lt_min hr hs, ?_⟩
    rintro z ⟨U, (rfl | hU), hzU⟩
    · exact le_trans (min_le_left _ _) (hrU z hzU)
    · exact le_trans (min_le_right _ _) (hsG z ⟨U, hU, hzU⟩)

/-! @end -/

/--
@problem compact_closed
@title A Compact Set in a Metric Space is Closed
@concept compact_metric

@preamble
Let `K` be compact and let `x` lie outside it. Around each point `y` of `K` draw the ball of radius half the distance from `x` to `y`. Those balls cover `K`, and by compactness finitely many of them do.

Each of the finitely many keeps a positive distance from `x`, so together they keep the smallest of those distances, `r`. The ball of radius `r` about `x` therefore meets none of them, and so meets none of `K`. Every point outside `K` has room around it, which is what it means for the complement to be open.
@description
Prove `MetricSpace.isClosed_of_isCompact`. Unfolding the goal leaves a point `x` of `Kᶜ` and asks for a radius; the cover is `{U | ∃ y ∈ K, U = MetricSpace.ball M y (M.dist x y / 2)}`, and the previous problem supplies both the positive distance each of its members keeps and the smallest distance the finitely many kept members keep together.
-/
theorem MetricSpace.isClosed_of_isCompact {X : Type u} (M : MetricSpace X) {K : Set X}
    (hK : M.toTopologicalSpace.IsCompact K) : M.toTopologicalSpace.IsClosed K := by
  intro x hx
  have hpos : ∀ y ∈ K, 0 < M.dist x y / 2 := fun y hy =>
    MetricSpace.half_dist_pos M (by rintro rfl; exact hx hy)
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hK {U | ∃ y ∈ K, U = MetricSpace.ball M y (M.dist x y / 2)}
    (by rintro U ⟨y, -, rfl⟩; exact MetricSpace.isOpenSet_ball M y _)
    (fun y hy => ⟨_, ⟨y, hy, rfl⟩, by
      rw [MetricSpace.mem_ball M, MetricSpace.dist_self M]; exact hpos y hy⟩)
  obtain ⟨r, hr, hrG⟩ := MetricSpace.exists_dist_ge_sUnion M hGfin (by
    rintro U hU
    obtain ⟨y, hy, rfl⟩ := hGF hU
    exact ⟨_, hpos y hy, fun z hz => MetricSpace.le_dist_of_mem_ball_half M hz⟩)
  refine ⟨r, hr, fun z hz hzK => ?_⟩
  have h1 : M.dist x z < r := hz
  linarith [hrG z (hGcov hzK)]

/-!
@concept compact_images
@title Compactness Under Continuous Maps
@kind theorem

A continuous map cannot spread a compact set out: pull a cover of the image back and it covers the set, so finitely many patches suffice on both sides. Nothing a topology can see then tells a compact space from a non-compact one. On the line the consequence is the theorem calculus claims as its own — a continuous function on a compact set attains its largest and its smallest value.
-/

/--
@problem compact_image
@title The Continuous Image of a Compact Set
@concept compact_images

@preamble
Let `f` be continuous and `S` compact, and let `F` cover `f '' S`. The preimages of the members of `F` are open and they cover `S`, so finitely many of them do — and the members of `F` those came from are finitely many and cover the image.

Naming those members is the one delicate step. A preimage does not remember the set it came from, so we choose one for each member `V` of the finite subcollection: `hGF hV` is the proof that `V` is a preimage, and its `choose` is the set chosen.
@description
Prove `TopologicalSpace.isCompact_image`. The pulled-back cover is `{V | ∃ U ∈ F, V = f ⁻¹' U}`. The subcollection to offer is `{U | ∃ V, ∃ hV : V ∈ G, (hGF hV).choose = U}`, written in exactly that order because `Set.Finite.dependent_image` — which proves it finite — is stated that way round.
-/
theorem TopologicalSpace.isCompact_image {X : Type u} {Y : Type v} (T : TopologicalSpace X)
    {T' : TopologicalSpace Y}
    {f : X → Y} (hf : T.Continuous T' f) {S : Set X} (hS : T.IsCompact S) :
    T'.IsCompact (f '' S) := by
  intro F hFo hcov
  have hpre : S ⊆ ⋃₀ {V | ∃ U ∈ F, V = f ⁻¹' U} := by
    intro x hxS
    obtain ⟨U, hUF, hxU⟩ := hcov ⟨x, hxS, rfl⟩
    exact ⟨f ⁻¹' U, ⟨U, hUF, rfl⟩, hxU⟩
  obtain ⟨G, hGF, hGfin, hGcov⟩ := hS {V | ∃ U ∈ F, V = f ⁻¹' U}
    (by rintro V ⟨U, hUF, rfl⟩; exact hf U (hFo U hUF)) hpre
  refine ⟨{U | ∃ V, ∃ hV : V ∈ G, (hGF hV).choose = U}, ?_, hGfin.dependent_image _, ?_⟩
  · rintro U ⟨V, hV, rfl⟩
    exact (hGF hV).choose_spec.1
  · rintro y ⟨x, hxS, rfl⟩
    obtain ⟨V, hVG, hxV⟩ := hGcov hxS
    rw [(hGF hVG).choose_spec.2] at hxV
    exact ⟨(hGF hVG).choose, ⟨V, hVG, rfl⟩, hxV⟩

/--
@problem homeomorphic_compact
@title Compactness is a Topological Property
@concept compact_images

@preamble
Homeomorphic spaces are the same space as far as a topology can tell, and compactness is stated with open sets alone, so it passes from either to the other.

No new argument is needed. A homeomorphism is onto, so the image of the whole of the first space is the whole of the second; and the image of a compact set is compact. The same reasoning showed connectedness to be a topological property, and it will show as much of any property written in open sets.
@description
Show `Homeomorphic.isCompactSpace`. `obtain ⟨e⟩` opens the existence of a homeomorphism, and `Set.image_univ` with `Set.range_eq_univ` turns the image of the whole space into the whole space, which is where `Homeomorph.surjective` is wanted.
-/
theorem Homeomorphic.isCompactSpace {X : Type u} {Y : Type v} {T : TopologicalSpace X}
    {T' : TopologicalSpace Y}
    (h : Homeomorphic T T') (hT : T.IsCompactSpace) : T'.IsCompactSpace := by
  obtain ⟨e⟩ := h
  have him := TopologicalSpace.isCompact_image T e.continuous_toFun hT
  rwa [Set.image_univ, Set.range_eq_univ.mpr (Homeomorph.surjective e)] at him

/--
@problem line_bounds
@title Bounded Above and Bounded Below
@concept compact_images

@preamble
A set of reals inside a ball is bounded in the order as well as in the metric. The ball about `c` of radius `ε` is the stretch from `c - ε` to `c + ε`, so `c + ε` is above every point of the set and `c - ε` below every point.

`BddAbove S` says some real is an upper bound of `S`, and `BddBelow S` that some real is a lower bound. They are what the least upper bound property asks for, and the next problem needs both.
@description
Prove `line_bddAbove_bddBelow`. A bound is offered as a pair of the number and the proof that it bounds. Restate each membership in the ball as the inequality `|c - x| < ε` that it abbreviates, split it with `abs_lt`, and let `linarith` finish.
-/
theorem line_bddAbove_bddBelow {K : Set ℝ} (h : line.IsBounded K) : BddAbove K ∧ BddBelow K := by
  obtain ⟨c, ε, hsub⟩ := h
  constructor
  · refine ⟨c + ε, fun x hx => ?_⟩
    have hx' : |c - x| < ε := hsub hx
    rw [abs_lt] at hx'
    linarith [hx'.1]
  · refine ⟨c - ε, fun x hx => ?_⟩
    have hx' : |c - x| < ε := hsub hx
    rw [abs_lt] at hx'
    linarith [hx'.2]

/-!
@problem line_extrema
@title A Compact Set of Reals Has a Largest and a Smallest Element
@concept compact_images

@preamble
A nonempty compact set of reals is bounded, so it has a least upper bound `a`; and it is closed, so it holds `a`. The second half is the substance: every stretch reaching down from `a` holds a point of the set, since otherwise its lower end would be a smaller upper bound, and a point found in every ball about `a` puts `a` in the closure.

The smallest element needs no new argument. Reflect the set in the origin — the map is continuous and carries compact to compact — take the largest element of the reflection, and reflect it back.
@description
Prove `line_exists_max` and `line_exists_min`. `Real.exists_isLUB` supplies the bound, `hlub.1` is its upper-bound half and `hlub.exists_between` produces a member of the set above `a - δ`; `MetricSpace.mem_closure_iff` is the ball form of membership in a closure. For the second, `line_continuous_affine_top (-1) 0` is the reflection.
-/

theorem line_exists_max {K : Set ℝ} (hK : line.toTopologicalSpace.IsCompact K) (hne : K.Nonempty) :
    ∃ a ∈ K, ∀ x ∈ K, x ≤ a := by
  obtain ⟨a, hlub⟩ := Real.exists_isLUB hne
    (line_bddAbove_bddBelow (MetricSpace.isBounded_of_isCompact line hK hne)).1
  refine ⟨a, ?_, fun x hx => hlub.1 hx⟩
  have hcl : line.toTopologicalSpace.closure K = K :=
    (TopologicalSpace.isClosed_iff_closure_eq line.toTopologicalSpace K).mp
      (MetricSpace.isClosed_of_isCompact line hK)
  rw [← hcl, MetricSpace.mem_closure_iff]
  intro δ hδ
  obtain ⟨y, hyK, hy1, hy2⟩ := hlub.exists_between (show a - δ < a by linarith)
  refine ⟨y, ?_, hyK⟩
  show |a - y| < δ
  rw [abs_lt]
  constructor <;> linarith

theorem line_exists_min {K : Set ℝ} (hK : line.toTopologicalSpace.IsCompact K) (hne : K.Nonempty) :
    ∃ a ∈ K, ∀ x ∈ K, a ≤ x := by
  have hc : line.toTopologicalSpace.IsCompact ((fun x => -1 * x + 0) '' K) :=
    TopologicalSpace.isCompact_image line.toTopologicalSpace
      (line_continuous_affine_top (-1) 0 (by norm_num)) hK
  obtain ⟨b, ⟨a, haK, hab⟩, hmax⟩ := line_exists_max hc (hne.image _)
  refine ⟨a, haK, fun x hx => ?_⟩
  have h := hmax (-1 * x + 0) ⟨x, hx, rfl⟩
  rw [← hab] at h
  linarith

/-! @end -/

/-!
@problem extreme_value
@title The Extreme Value Theorem
@concept compact_images

@preamble
A continuous real-valued function on a nonempty compact set attains its largest and its smallest value. There is no calculation left to do: the image of the set is a compact set of reals, which has a largest element, and that element is the value of the function at some point of the set.

What the theorem needs of the domain is only compactness. It is a statement about any space at all, and the closed interval enters only when one asks which sets of reals are compact.
@description
Prove `TopologicalSpace.exists_max_of_isCompact` and `TopologicalSpace.exists_min_of_isCompact`. Apply the previous problem to the image, whose compactness is `TopologicalSpace.isCompact_image` and whose nonemptiness is `Set.Nonempty.image`; `obtain ⟨a, haS, rfl⟩` then names the point the largest value is taken at.
-/

theorem TopologicalSpace.exists_max_of_isCompact {X : Type u} (T : TopologicalSpace X) {f : X → ℝ}
    (hf : T.Continuous line.toTopologicalSpace f) {S : Set X} (hS : T.IsCompact S)
      (hne : S.Nonempty) :
    ∃ a ∈ S, ∀ x ∈ S, f x ≤ f a := by
  obtain ⟨b, hbK, hbmax⟩ :=
    line_exists_max (TopologicalSpace.isCompact_image T hf hS) (hne.image f)
  obtain ⟨a, haS, rfl⟩ := hbK
  exact ⟨a, haS, fun x hx => hbmax (f x) ⟨x, hx, rfl⟩⟩

theorem TopologicalSpace.exists_min_of_isCompact {X : Type u} (T : TopologicalSpace X) {f : X → ℝ}
    (hf : T.Continuous line.toTopologicalSpace f) {S : Set X} (hS : T.IsCompact S)
      (hne : S.Nonempty) :
    ∃ a ∈ S, ∀ x ∈ S, f a ≤ f x := by
  obtain ⟨b, hbK, hbmin⟩ :=
    line_exists_min (TopologicalSpace.isCompact_image T hf hS) (hne.image f)
  obtain ⟨a, haS, rfl⟩ := hbK
  exact ⟨a, haS, fun x hx => hbmin (f x) ⟨x, hx, rfl⟩⟩

/-! @end -/

/-!
@concept interval_compact
@title The Closed Interval
@kind theorem

The unit interval is compact, and the least upper bound property is what says so. It is the deepest fact in this section, and it is the reason the theorems above it are theorems of calculus: they hold on a closed interval because a closed interval is compact.
-/

/-!
@problem define_covered
@title The Points Covered So Far
@concept interval_compact

@preamble
Fix a collection `F` of open sets covering the unit interval. Say that `F` *covers up to* `x` when finitely many of its members already cover the stretch from `0` to `x`. What is to be proved is that `F` covers up to `1`, since that stretch is the interval itself.

It covers up to `0` at once. The stretch from `0` to `0` is the single point `0`, and one member of the collection holds it.
@description
Define `CoveredUpTo F x`: some `G ⊆ F` has `G.Finite` and `{y | 0 ≤ y ∧ y ≤ x} ⊆ ⋃₀ G`, those two conjuncts in that order. Then prove `coveredUpTo_zero`. A point of the stretch from `0` to `0` is squeezed between two inequalities, and `le_antisymm` turns them into the equation that rewrites it to `0`.
-/

def CoveredUpTo (F : Set (Set ℝ)) (x : ℝ) : Prop :=
  ∃ G ⊆ F, G.Finite ∧ {y | 0 ≤ y ∧ y ≤ x} ⊆ ⋃₀ G

theorem coveredUpTo_zero {F : Set (Set ℝ)} (hcov : unitInterval ⊆ ⋃₀ F) : CoveredUpTo F 0 := by
  obtain ⟨U, hUF, hU⟩ := hcov ⟨le_refl 0, zero_le_one⟩
  refine ⟨{U}, Set.singleton_subset_iff.mpr hUF, Set.finite_singleton U, ?_⟩
  rintro y ⟨hy0, hy1⟩
  rw [le_antisymm hy1 hy0]
  exact ⟨U, rfl, hU⟩

/-- @spec -/
example (F : Set (Set ℝ)) (x : ℝ) :
    CoveredUpTo F x ↔ ∃ G ⊆ F, G.Finite ∧ {y | 0 ≤ y ∧ y ≤ x} ⊆ ⋃₀ G := Iff.rfl

/-! @end -/

/--
@problem covered_insert
@title Adding One Patch
@concept interval_compact

@preamble
Suppose `F` covers up to `x`, and let `U` be one of its members holding every point between `x` and some further point `z`. Add `U` to the finitely many sets already kept: one more set is still finitely many, and the enlarged collection covers the stretch from `0` to `z`, since a point of it is either at `x` or below — where the old sets reach — or beyond, where `U` does.
@description
Prove `coveredUpTo_insert`. `insert U G` adds a set to a collection, `Set.insert_subset` shows the result still inside `F` and `Set.Finite.insert` that it is still finite; `by_cases` on whether the point is past `x` chooses which half of the argument applies, and `Set.sUnion_mono` carries the old union into the new one.
-/
theorem coveredUpTo_insert {F : Set (Set ℝ)} {U : Set ℝ} (hUF : U ∈ F) {x z : ℝ}
    (h : CoveredUpTo F x) (hU : ∀ y, x < y → y ≤ z → y ∈ U) : CoveredUpTo F z := by
  obtain ⟨G, hGF, hGfin, hGcov⟩ := h
  refine ⟨insert U G, Set.insert_subset hUF hGF, hGfin.insert U, ?_⟩
  rintro y ⟨hy0, hyz⟩
  by_cases hyx : y ≤ x
  · exact Set.sUnion_mono (Set.subset_insert U G) (hGcov ⟨hy0, hyx⟩)
  · exact ⟨U, Set.mem_insert U G, hU y (not_le.mp hyx) hyz⟩

/--
@problem covered_lub
@title Past the Supremum
@concept interval_compact

@preamble
Collect the points of the interval that `F` covers up to, and let `c` be the least upper bound of that collection. Some member `U` of `F` holds `c`, and being open it holds a whole stretch around `c`, say of radius `ε`.

A least upper bound is approached from within, so the collection holds a point `x` above `c - ε`. Then `F` covers up to `x`, and `U` holds every point from `x` up to anything short of `c + ε` — every such point being within `ε` of `c`. So `F` covers up to every non-negative point short of `c + ε`: the supremum is not a barrier but a place where the cover reaches past itself.
@description
Prove `exists_coveredUpTo_of_isLUB`. `hlub.exists_between` produces the point above `c - ε`, the previous problem adds `U` to what it reached, and restating a membership in a ball as `|c - y| < ε` leaves two inequalities for `linarith`.
-/
theorem exists_coveredUpTo_of_isLUB {F : Set (Set ℝ)}
    (hFo : ∀ U ∈ F, line.toTopologicalSpace.IsOpen U) (hFcov : unitInterval ⊆ ⋃₀ F) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hlub : IsLUB {x | 0 ≤ x ∧ x ≤ 1 ∧ CoveredUpTo F x} c) :
    ∃ δ > 0, ∀ z, 0 ≤ z → z < c + δ → CoveredUpTo F z := by
  obtain ⟨U, hUF, hcU⟩ := hFcov ⟨hc0, hc1⟩
  obtain ⟨ε, hε, hball⟩ := hFo U hUF c hcU
  obtain ⟨x, hxA, hxgt, hxle⟩ := hlub.exists_between (show c - ε < c by linarith)
  refine ⟨ε, hε, fun z hz0 hzc => coveredUpTo_insert hUF hxA.2.2 (fun y hy1 hy2 => hball ?_)⟩
  show |c - y| < ε
  rw [abs_lt]
  constructor <;> linarith

/-!
@problem interval_compact
@title The Unit Interval is Compact
@concept interval_compact

@preamble
Let `F` be an open cover of the unit interval and let `c` be the least upper bound of the points it covers up to. It exists: `0` is such a point and `1` bounds them all. And `c` lies in the interval, so the last problem applies: it gives a radius `δ` such that `F` covers up to every non-negative point short of `c + δ`.

Then `c` is `1`. If it were less, a point between `c` and the smaller of `1` and `c + δ` would be covered up to and would be a point of the interval above the least upper bound. So `F` covers up to `1`, which is the finite subcover wanted.

The extreme value theorem of calculus follows: a continuous function on the unit interval attains its largest value.
@description
Prove `unitInterval_isCompact` and then `unitInterval_exists_max`. `Real.exists_isLUB` supplies `c` from the point `0` and the bound `1`; `hlub.1` is the upper-bound half and `hlub.2` the least half. The second is the extreme value theorem at this set, whose nonemptiness is witnessed by `0`.
-/

theorem unitInterval_isCompact : line.toTopologicalSpace.IsCompact unitInterval := by
  intro F hFo hFcov
  obtain ⟨c, hlub⟩ := Real.exists_isLUB (s := {x | 0 ≤ x ∧ x ≤ 1 ∧ CoveredUpTo F x})
    ⟨0, le_refl 0, zero_le_one, coveredUpTo_zero hFcov⟩ ⟨1, fun x hx => hx.2.1⟩
  have hc0 : 0 ≤ c := hlub.1 ⟨le_refl 0, zero_le_one, coveredUpTo_zero hFcov⟩
  have hc1 : c ≤ 1 := hlub.2 (fun x hx => hx.2.1)
  obtain ⟨δ, hδ, key⟩ := exists_coveredUpTo_of_isLUB hFo hFcov hc0 hc1 hlub
  have hc : (1 : ℝ) ≤ c := by
    by_contra hne
    have hlt : c < 1 := not_le.mp hne
    have hz0 : (0 : ℝ) ≤ min 1 (c + δ / 2) := le_min zero_le_one (by linarith)
    have hzlt : min 1 (c + δ / 2) < c + δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact absurd (hlub.1 ⟨hz0, min_le_left _ _, key _ hz0 hzlt⟩)
      (not_le.mpr (lt_min hlt (by linarith)))
  exact key 1 zero_le_one (by linarith)

theorem unitInterval_exists_max {f : ℝ → ℝ}
    (hf : line.toTopologicalSpace.Continuous line.toTopologicalSpace f) :
    ∃ a ∈ unitInterval, ∀ x ∈ unitInterval, f x ≤ f a :=
  TopologicalSpace.exists_max_of_isCompact line.toTopologicalSpace hf unitInterval_isCompact
    ⟨0, le_refl 0, zero_le_one⟩

/-! @end -/

end GeneralTopology
