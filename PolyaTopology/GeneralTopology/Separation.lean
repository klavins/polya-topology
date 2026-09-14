import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Quotients

/-! @section Separation Axioms -/

universe u v

namespace GeneralTopology

/-!
@concept separation_axioms
@title The First Three Separation Axioms
@kind definition

A topology need not tell its points apart: the indiscrete one cannot distinguish any two of them. The separation axioms say how well a given topology can, each asking for open sets around distinct points and each stronger than the one before. They are the first thing asked of a space once it exists, and most of what follows assumes one of them.
-/

/-!
@problem define_separation_axioms
@title The Axioms T₀, T₁ and Hausdorff
@concept separation_axioms

@preamble
Let `x` and `y` be distinct points of a space. Three conditions, in increasing strength, ask the open sets to notice the difference.

T₀ asks that one of the two points have an open set around it leaving the other out. Which of the two is not said, so the condition is a disjunction.

T₁ asks it of both points at once: each has an open set around it that the other escapes.

T₂, or *Hausdorff*, asks more. Each point has an open set around it and the two sets are disjoint, so the points are not merely distinguished but held apart.
@description
Define `TopologicalSpace.IsT0`, `TopologicalSpace.IsT1` and `TopologicalSpace.IsT2`, each quantified over `x y : X` with `x ≠ y`. Write T₁ as `∃ U, T.IsOpen U ∧ x ∈ U ∧ y ∉ U`; T₀ as that disjunct or the same with the two points exchanged; and Hausdorff as `∃ U V` with the five conditions `T.IsOpen U`, `T.IsOpen V`, `x ∈ U`, `y ∈ V`, `U ∩ V = ∅`, in that order.
-/

def TopologicalSpace.IsT0 {X : Type u} (T : TopologicalSpace X) : Prop :=
  ∀ x y : X, x ≠ y →
    (∃ U, T.IsOpen U ∧ x ∈ U ∧ y ∉ U) ∨ (∃ V, T.IsOpen V ∧ y ∈ V ∧ x ∉ V)

def TopologicalSpace.IsT1 {X : Type u} (T : TopologicalSpace X) : Prop :=
  ∀ x y : X, x ≠ y → ∃ U, T.IsOpen U ∧ x ∈ U ∧ y ∉ U

def TopologicalSpace.IsT2 {X : Type u} (T : TopologicalSpace X) : Prop :=
  ∀ x y : X, x ≠ y → ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

/-- @spec -/
example (X : Type) (T : TopologicalSpace X) :
    (T.IsT0 ↔ ∀ x y : X, x ≠ y →
        (∃ U, T.IsOpen U ∧ x ∈ U ∧ y ∉ U) ∨ (∃ V, T.IsOpen V ∧ y ∈ V ∧ x ∉ V))
      ∧ (T.IsT1 ↔ ∀ x y : X, x ≠ y → ∃ U, T.IsOpen U ∧ x ∈ U ∧ y ∉ U)
      ∧ (T.IsT2 ↔ ∀ x y : X, x ≠ y →
        ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! @end -/

/-!
@problem separation_implications
@title Each Axiom Implies the One Before
@concept separation_axioms

@preamble
The conditions grow stronger, so each implies its predecessor, and neither proof needs more than the definitions.

T₁ gives T₀ by taking the left disjunct: the set it supplies around `x` is offered, and the other alternative is never reached.

Hausdorff gives T₁ by forgetting `V`. The set `U` around `x` already leaves `y` out, because `y` lies in `V` and the two sets meet nowhere: a point in both would lie in `U ∩ V`, which is empty.
@description
Prove `TopologicalSpace.isT0_of_isT1` and `TopologicalSpace.isT1_of_isT2`. For the second, assume `y ∈ U`, put `y` into `U ∩ V` with an anonymous constructor, rewrite by the hypothesis that this set is empty, and a membership in `∅` is absurd.
-/

theorem TopologicalSpace.isT0_of_isT1 {X : Type u} {T : TopologicalSpace X} (h : T.IsT1) : T.IsT0 :=
  fun x y hxy => Or.inl (h x y hxy)

theorem TopologicalSpace.isT1_of_isT2 {X : Type u} {T : TopologicalSpace X} (h : T.IsT2) :
    T.IsT1 := by
  intro x y hxy
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := h x y hxy
  refine ⟨U, hU, hxU, ?_⟩
  intro hyU
  have hy : y ∈ U ∩ V := ⟨hyU, hyV⟩
  rw [hUV] at hy
  exact hy

/-! @end -/

/-!
@concept separation_examples
@title Spaces That Separate, and Spaces That Do Not
@kind theorem

An axiom earns its place by what it admits and what it rules out. Every metric space satisfies all three of these, and the example spaces of the earlier sections sit at every level of the hierarchy — which is what shows that no two of the three conditions are the same condition.
-/

/--
@problem metric_dist_pos
@title Distinct Points Lie a Positive Distance Apart
@concept separation_examples

@preamble
The axioms give `M.dist x y = 0` exactly when `x = y`, and the distance is never negative. Between distinct points it is therefore strictly positive.

That is the fact every separation argument in a metric space begins with, since the radius it works with is read off from it. A real number that is at least `0` is either greater than `0` or equal to it, which is what `lt_or_eq_of_le` says of `MetricSpace.nonneg M x y`.
@description
Show that `0 < M.dist x y` when `x ≠ y`. Split the non-negativity with `lt_or_eq_of_le`; in the second case `M.dist_eq_zero` turns the equation into `x = y`, which the hypothesis refutes.
-/
theorem MetricSpace.dist_pos {X : Type u} (M : MetricSpace X) {x y : X} (h : x ≠ y) : 0 < M.dist x y
    := by
  rcases lt_or_eq_of_le (MetricSpace.nonneg M x y) with hlt | heq
  · exact hlt
  · exact absurd (M.dist_eq_zero.mp heq.symm) h

/--
@problem metric_hausdorff
@title Every Metric Space is Hausdorff
@concept separation_examples

@preamble
Two distinct points are a positive distance `d` apart. Put a ball of radius `d / 2` about each of them.

A point in both balls would be within `d / 2` of `x` and within `d / 2` of `y`, so the journey from `x` to `y` through it would be shorter than `d` — and the triangle inequality says that no journey from `x` to `y` is shorter than `d`. The two balls are therefore disjoint.

So a metric space satisfies the strongest of the three axioms, and by the implications above all three. This is the reason the axioms are worth imposing: they are the conditions that hold wherever there is a distance.
@description
Show that `M.toTopologicalSpace.IsT2`. Offer the two balls of radius `M.dist x y / 2`, whose openness and two memberships are `MetricSpace.isOpenSet_ball` and `MetricSpace.mem_ball_self`. For the emptiness, `Set.eq_empty_of_forall_notMem` takes a point of the intersection apart; `M.dist_triangle x z y` and `M.dist_comm` then leave the contradiction to `linarith`.
-/
theorem MetricSpace.isT2 {X : Type u} (M : MetricSpace X) : M.toTopologicalSpace.IsT2 := by
  intro x y hxy
  have h0 : 0 < M.dist x y := MetricSpace.dist_pos M hxy
  refine ⟨M.ball x (M.dist x y / 2), M.ball y (M.dist x y / 2), MetricSpace.isOpenSet_ball M x _,
    MetricSpace.isOpenSet_ball M y _, MetricSpace.mem_ball_self M x _ (by linarith),
    MetricSpace.mem_ball_self M y _ (by linarith), ?_⟩
  apply Set.eq_empty_of_forall_notMem
  rintro z ⟨hz1, hz2⟩
  rw [MetricSpace.mem_ball M] at hz1 hz2
  have e : M.dist y z = M.dist z y := M.dist_comm
  have ht := M.dist_triangle x z y
  linarith

/--
@problem codiscrete_not_separated
@title The Indiscrete Topology Separates Nothing
@concept separation_examples

@preamble
At the other end stands the topology whose only open sets are the empty one and the whole space. It cannot tell any two points apart: an open set containing one of them is not empty, so it is everything, and it contains the other as well.

A set with two distinct points therefore fails even T₀ under that topology, the weakest of the three conditions. Separation is a demand for open sets, and this topology has none to spare.
@description
Show that `(indiscrete X).IsT0` is false when `X` has two distinct points `x` and `y`. Take the disjunction apart with `rcases`, and in each branch `rcases` the openness, which says the set is `∅` or `Set.univ`; the first case contradicts a membership and the second a non-membership, which `trivial` supplies.
-/
theorem indiscrete_not_isT0 {X : Type u} {x y : X} (h : x ≠ y) : ¬ (indiscrete X).IsT0 := by
  intro hT
  rcases hT x y h with ⟨U, hU, hxU, hyU⟩ | ⟨U, hU, hyU, hxU⟩ <;> rcases hU with rfl | rfl
  · exact hxU
  · exact hyU trivial
  · exact hyU
  · exact hxU trivial

/-!
@problem sierpinski_separation
@title The Sierpiński Space is T₀ and Not T₁
@concept separation_examples

@preamble
The two-point space with one open point sits exactly between the first two axioms, which is what makes it the standard counterexample.

It is T₀. The set `{true}` is open, it contains `true`, and it leaves `false` out — so whichever way round two distinct points of `Bool` arrive, one of the two disjuncts is satisfied by that one set.

It is not T₁. The open sets were defined so that any one containing `false` contains `true` as well, so no open set separates `false` from `true` at all, and the other disjunct is the only one available.
@description
Prove `sierpinski_isT0` and `sierpinski_not_isT1`. For the first, `cases x <;> cases y` leaves four goals, two of which `x ≠ y` refutes; the openness of `{true}` is an implication whose hypothesis is not needed. For the second, apply the assumption at `false` and `true` and then apply the openness of the set it returns.
-/

theorem sierpinski_isT0 : sierpinski.IsT0 := by
  intro x y hxy
  cases x <;> cases y
  · exact absurd rfl hxy
  · exact Or.inr ⟨{true}, fun _ => rfl, rfl, by simp⟩
  · exact Or.inl ⟨{true}, fun _ => rfl, rfl, by simp⟩
  · exact absurd rfl hxy

theorem sierpinski_not_isT1 : ¬ sierpinski.IsT1 := by
  intro h
  obtain ⟨U, hU, hfU, htU⟩ := h false true (by simp)
  exact htU (hU hfU)

/-! @end -/

/-!
@problem cofinite_separation
@title The Cofinite Topology is T₁ and Not Hausdorff
@concept separation_examples

@preamble
One level higher, the gap between T₁ and Hausdorff opens.

The cofinite topology is T₁ on any set. The complement of a single point is open, since its own complement is that one point and a point is a finite set, and it contains every other point of the space.

On an infinite set it is not Hausdorff, because its open sets are too large to avoid one another. If two of them were disjoint and nonempty, their complements would have finite size and would cover everything between them — so the whole set would be finite.
@description
Prove `cofinite_isT1` for any `X`, and `cofinite_not_isT2` for `ℕ`. In the first, `compl_compl` and `Set.finite_singleton` show `{y}ᶜ` open. In the second, `Or.resolve_left` turns each open set's disjunction into the finiteness of its complement, `Set.compl_inter` rewrites `Set.univ` as the union of the two complements, and `Set.infinite_univ` refutes its finiteness.
-/

theorem cofinite_isT1 {X : Type u} : (cofinite X).IsT1 := by
  intro x y hxy
  refine ⟨{y}ᶜ, Or.inr ?_, hxy, ?_⟩
  · rw [compl_compl]
    exact Set.finite_singleton y
  · intro h
    exact h rfl

theorem cofinite_not_isT2 : ¬ (cofinite ℕ).IsT2 := by
  intro h
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := h 0 1 (by norm_num)
  have hUc : Uᶜ.Finite := hU.resolve_left (fun he => by rw [he] at hxU; exact hxU)
  have hVc : Vᶜ.Finite := hV.resolve_left (fun he => by rw [he] at hyV; exact hyV)
  have e : (Set.univ : Set ℕ) = Uᶜ ∪ Vᶜ := by
    rw [← Set.compl_inter, hUV, Set.compl_empty]
  exact Set.infinite_univ (by rw [e]; exact hUc.union hVc)

/-! @end -/

/-!
@concept separation_closures
@title Separation Read Through Closures
@kind theorem

Each of the three axioms is a demand for open sets around points, and each has an equivalent form stated with the closure instead. The translations are what make the axioms usable, since they replace a search for open sets by an equation between sets — and the Hausdorff one is where the product topology earns its place.
-/

/-!
@problem closure_of_a_point
@title The Closure of a Single Point
@concept separation_closures

@preamble
What does closing one point add? A point `x` lies in the closure of `{y}` when every neighbourhood of `x` meets `{y}`, which is to say contains `y`. Only the open sets need be tested, since every neighbourhood has one inside it.

So `x ∈ T.closure {y}` says exactly: every open set containing `x` contains `y`.

Read as a comparison, that same condition says the closure of `{x}` lies inside the closure of `{y}`. The closure of `{y}` is a closed set, so it contains the closure of `{x}` exactly when it contains `x`.
@description
Prove `TopologicalSpace.mem_closure_singleton` and `TopologicalSpace.closure_singleton_iff`. Both rest on `TopologicalSpace.mem_closure_iff` and `TopologicalSpace.nbhd_of_isOpen`; a membership in a singleton is an equation, which `show` restates for `rw`. The second reads the first at `x` and closes its other direction with `TopologicalSpace.closure_min`.
-/

theorem TopologicalSpace.mem_closure_singleton {X : Type u} (T : TopologicalSpace X) {x y : X} :
    x ∈ T.closure {y} ↔ ∀ U, T.IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro hx U hU hxU
    obtain ⟨z, hzU, hzy⟩ :=
      (TopologicalSpace.mem_closure_iff T).mp hx U (TopologicalSpace.nbhd_of_isOpen T hU hxU)
    rw [show z = y from hzy] at hzU
    exact hzU
  · intro h
    apply (TopologicalSpace.mem_closure_iff T).mpr
    rintro N ⟨U, hU, hxU, hUN⟩
    exact ⟨y, hUN (h U hU hxU), rfl⟩

theorem TopologicalSpace.closure_singleton_iff {X : Type u} (T : TopologicalSpace X) {x y : X} :
    T.closure {x} ⊆ T.closure {y} ↔ ∀ U, T.IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro h
    exact (TopologicalSpace.mem_closure_singleton T).mp
      (h (TopologicalSpace.subset_closure T {x} rfl))
  · intro h
    refine TopologicalSpace.closure_min T (TopologicalSpace.isClosed_closure T {y}) ?_
    intro z hz
    rw [show z = x from hz]
    exact (TopologicalSpace.mem_closure_singleton T).mpr h

/-! @end -/

/--
@problem t1_iff_points_closed
@title T₁ Means Every Point is Closed
@concept separation_closures

@preamble
The axiom T₁ has a one-word form: the points of the space are closed sets.

If the points are closed then, given `x ≠ y`, the set `{y}ᶜ` is open, it contains `x`, and it leaves `y` out — which is the axiom.

Conversely, suppose the axiom holds, and look at `{x}ᶜ`. Each of its points `y` is distinct from `x`, so the axiom supplies an open set holding `y` and missing `x`; an open set missing `x` lies inside `{x}ᶜ`. So `{x}ᶜ` is a neighbourhood of each of its own points, and is therefore open.
@description
Prove `TopologicalSpace.isT1_iff_isClosed_singleton`. Forwards, restate the closedness with `show` and turn it into a statement at each point with `TopologicalSpace.isOpen_iff_nbhd`. A membership `y ∈ {x}` is the equation `y = x`, so a point of `{x}ᶜ` arrives with exactly the hypothesis `y ≠ x` the axiom wants.
-/
theorem TopologicalSpace.isT1_iff_isClosed_singleton {X : Type u} (T : TopologicalSpace X) :
    T.IsT1 ↔ ∀ x : X, T.IsClosed {x} := by
  constructor
  · intro h x
    show T.IsOpen _
    rw [TopologicalSpace.isOpen_iff_nbhd]
    intro y hy
    obtain ⟨U, hU, hyU, hxU⟩ := h y x hy
    exact ⟨U, hU, hyU, fun z hz he => hxU (by rw [← show z = x from he]; exact hz)⟩
  · intro h x y hxy
    exact ⟨{y}ᶜ, h y, hxy, fun hn => hn rfl⟩

/--
@problem t0_iff_closures
@title T₀ Means Distinct Points Have Distinct Closures
@concept separation_closures

@preamble
The weakest axiom has a closure form as well. Two points are indistinguishable when no open set holds one without the other, and by the problem above that is exactly the statement that each lies in the closure of the other — that the two closures are equal.

So T₀ says that the closure of a point determines the point: the assignment carrying `x` to `T.closure {x}` is injective. Where T₀ fails, two different points have the very same closure, and nothing built out of open sets will ever separate them.
@description
Prove `TopologicalSpace.isT0_iff_closure_injective`, stating the right-hand side as `∀ x y, T.closure {x} = T.closure {y} → x = y`. Forwards, take the two containments out of the equation with `.subset` and `.symm.subset` and read them through `TopologicalSpace.closure_singleton_iff`; the axiom's two branches then contradict them. Backwards, `by_contra` and `push Not at` turn the failure of the axiom into the two hypotheses that build the equation.
-/
theorem TopologicalSpace.isT0_iff_closure_injective {X : Type u} (T : TopologicalSpace X) :
    T.IsT0 ↔ ∀ x y : X, T.closure {x} = T.closure {y} → x = y := by
  constructor
  · intro h x y he
    by_contra hxy
    have h1 := (TopologicalSpace.closure_singleton_iff T).mp he.subset
    have h2 := (TopologicalSpace.closure_singleton_iff T).mp he.symm.subset
    rcases h x y hxy with ⟨U, hU, hxU, hyU⟩ | ⟨U, hU, hyU, hxU⟩
    · exact hyU (h1 U hU hxU)
    · exact hxU (h2 U hU hyU)
  · intro h x y hxy
    by_contra hc
    push Not at hc
    exact hxy (h x y (Set.Subset.antisymm
      ((TopologicalSpace.closure_singleton_iff T).mpr hc.1)
      ((TopologicalSpace.closure_singleton_iff T).mpr hc.2)))

/-!
@problem hausdorff_iff_diagonal
@title Hausdorff Means the Diagonal is Closed
@concept separation_closures

@preamble
The *diagonal* of a space is the set of pairs `(x, x)` inside `X × X`: a copy of the space sitting inside its own square. The Hausdorff condition is exactly the statement that this copy is closed there.

A point off the diagonal is a pair whose two coordinates differ. To say the complement of the diagonal is open is to put an open box `U ×ˢ V` around each such pair inside that complement — and a box misses the diagonal exactly when `U` and `V` are disjoint, since a point `z` of both would put the pair `(z, z)` inside the box.
@description
Prove `TopologicalSpace.isClosed_diagonal_of_isT2` and `TopologicalSpace.isT2_of_isClosed_diagonal`, both against `T.prod T`. Each restates the closedness with `show` and then reads the definition of the product topology directly: forwards the separating pair becomes the box, and backwards the box at `(x, y)` becomes the separating pair, with `(z, z)` the point that shows it disjoint.
-/

/-- @given -/
def diagonal (X : Type u) : Set (X × X) := {p | p.1 = p.2}

theorem TopologicalSpace.isClosed_diagonal_of_isT2 {X : Type u} {T : TopologicalSpace X}
    (h : T.IsT2) : (T.prod T).IsClosed (diagonal X) := by
  show (T.prod T).IsOpen _
  intro p hp
  obtain ⟨U, V, hU, hV, h1, h2, hUV⟩ := h p.1 p.2 hp
  refine ⟨U, V, hU, hV, ⟨h1, h2⟩, ?_⟩
  rintro q ⟨hq1, hq2⟩ he
  have hz : q.1 ∈ U ∩ V := ⟨hq1, by rw [show q.1 = q.2 from he]; exact hq2⟩
  rw [hUV] at hz
  exact hz

theorem TopologicalSpace.isT2_of_isClosed_diagonal {X : Type u} {T : TopologicalSpace X}
    (h : (T.prod T).IsClosed (diagonal X)) : T.IsT2 := by
  intro x y hxy
  obtain ⟨U, V, hU, hV, hp, hsub⟩ := h (x, y) hxy
  refine ⟨U, V, hU, hV, hp.1, hp.2, ?_⟩
  apply Set.eq_empty_of_forall_notMem
  rintro z ⟨hzU, hzV⟩
  exact hsub (show ((z, z) : X × X) ∈ U ×ˢ V from ⟨hzU, hzV⟩) rfl

/-! @end -/

/-!
@concept separation_hereditary
@title Which Constructions Keep the Axioms
@kind theorem

A property is worth naming when the constructions of the subject preserve it. The three axioms pass to a subspace, to a product of two spaces, and across a homeomorphism — the last because they are stated in open sets alone, which a homeomorphism matches one for one. A quotient is the exception: gluing points together can destroy any of the three.
-/

/-!
@problem subspace_separation
@title A Subspace Inherits All Three
@concept separation_hereditary

@preamble
A subset of a space carries the traces of the ambient open sets, and that is all three axioms need. Two distinct points of `A` are distinct as points of `X`, since they differ only by the proof each carries that it lies in `A`. Whatever open sets separate them in `X`, their traces separate them in `A`.

Disjointness survives too, because a preimage commutes with intersecting: the traces of two disjoint sets meet in the trace of the empty set, which is empty.
@description
Prove `TopologicalSpace.isT0_subspace`, `TopologicalSpace.isT1_subspace` and `TopologicalSpace.isT2_subspace`. In each, `Subtype.ext` turns an equality of the underlying points back into an equality of the points of `A`; the trace of an open `U` is open by `⟨U, hU, rfl⟩`, and `Set.preimage_inter` with `Set.preimage_empty` closes the last one.
-/

theorem TopologicalSpace.isT0_subspace {X : Type u} {T : TopologicalSpace X} (h : T.IsT0)
    (A : Set X) :
    (T.subspace A).IsT0 := by
  intro a b hab
  rcases h a.val b.val (fun e => hab (Subtype.ext e)) with ⟨U, hU, haU, hbU⟩ | ⟨U, hU, hbU, haU⟩
  · exact Or.inl ⟨Subtype.val ⁻¹' U, ⟨U, hU, rfl⟩, haU, hbU⟩
  · exact Or.inr ⟨Subtype.val ⁻¹' U, ⟨U, hU, rfl⟩, hbU, haU⟩

theorem TopologicalSpace.isT1_subspace {X : Type u} {T : TopologicalSpace X} (h : T.IsT1)
    (A : Set X) :
    (T.subspace A).IsT1 := by
  intro a b hab
  obtain ⟨U, hU, haU, hbU⟩ := h a.val b.val (fun e => hab (Subtype.ext e))
  exact ⟨Subtype.val ⁻¹' U, ⟨U, hU, rfl⟩, haU, hbU⟩

theorem TopologicalSpace.isT2_subspace {X : Type u} {T : TopologicalSpace X} (h : T.IsT2)
    (A : Set X) : (T.subspace A).IsT2 := by
  intro a b hab
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := h a.val b.val (fun e => hab (Subtype.ext e))
  refine ⟨Subtype.val ⁻¹' U, Subtype.val ⁻¹' V, ⟨U, hU, rfl⟩, ⟨V, hV, rfl⟩, haU, hbV, ?_⟩
  rw [← Set.preimage_inter, hUV, Set.preimage_empty]

/-! @end -/

/--
@problem product_hausdorff
@title A Product of Two Hausdorff Spaces
@concept separation_hereditary

@preamble
Two distinct points of a product differ in at least one coordinate. Suppose they differ in the first. The factor `X` is Hausdorff, so its two first coordinates have disjoint open sets around them — and pulling those back along the first projection gives two disjoint open sets of the product, one around each point.

The projections are continuous, which is what makes the preimages open, and a preimage commutes with intersecting, which is what keeps them disjoint. The case where the points differ in the second coordinate is the same argument along the second projection.
@description
Show that `(T.prod T').IsT2` when both factors are Hausdorff. Split on `p.1 = q.1` with `by_cases`; in the equal case `Prod.ext` shows the second coordinates differ. `TopologicalSpace.continuous_fst` and `TopologicalSpace.continuous_snd` supply the openness of the preimages, and `Set.preimage_inter` with `Set.preimage_empty` their disjointness.
-/
theorem TopologicalSpace.isT2_prod {X : Type u} {Y : Type v} {T : TopologicalSpace X}
    {T' : TopologicalSpace Y}
    (h : T.IsT2) (h' : T'.IsT2) : (T.prod T').IsT2 := by
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := h' p.2 q.2 (fun e => hpq (Prod.ext h1 e))
    refine ⟨Prod.snd ⁻¹' U, Prod.snd ⁻¹' V, TopologicalSpace.continuous_snd T T' U hU,
      TopologicalSpace.continuous_snd T T' V hV, hpU, hqV, ?_⟩
    rw [← Set.preimage_inter, hUV, Set.preimage_empty]
  · obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := h p.1 q.1 h1
    refine ⟨Prod.fst ⁻¹' U, Prod.fst ⁻¹' V, TopologicalSpace.continuous_fst T T' U hU,
      TopologicalSpace.continuous_fst T T' V hV, hpU, hqV, ?_⟩
    rw [← Set.preimage_inter, hUV, Set.preimage_empty]

/--
@problem hausdorff_invariant
@title Being Hausdorff is a Topological Property
@concept separation_hereditary

@preamble
Nothing in the Hausdorff condition mentions anything but open sets and points, so a homeomorphism carries it across. Given two distinct points of the second space, send them back by the inverse map — they are still distinct, since the forward map returns them — separate them there, and pull the two open sets forward along the inverse map, which is continuous.

Discreteness and indiscreteness were transported across a homeomorphism in an earlier section, and each of the other axioms here moves by the argument just given. A property that survives every homeomorphism is a property of the space and not of the names of its points.
@description
Show that `T'.IsT2` when `Homeomorphic T T'` and `T.IsT2`. Take the homeomorphism out of the hypothesis with `obtain ⟨e⟩`. The two open sets are `e.invFun ⁻¹' U` and `e.invFun ⁻¹' V`, open by `e.continuous_invFun`; `e.right_inv` is what shows the two pulled-back points distinct.
-/
theorem Homeomorphic.isT2 {X : Type u} {Y : Type v} {T : TopologicalSpace X}
    {T' : TopologicalSpace Y}
    (h : Homeomorphic T T') (hT : T.IsT2) : T'.IsT2 := by
  obtain ⟨e⟩ := h
  intro x y hxy
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := hT (e.invFun x) (e.invFun y)
    (fun he => hxy (by rw [← e.right_inv x, ← e.right_inv y, he]))
  refine ⟨e.invFun ⁻¹' U, e.invFun ⁻¹' V, e.continuous_invFun U hU, e.continuous_invFun V hV,
    hxU, hyV, ?_⟩
  rw [← Set.preimage_inter, hUV, Set.preimage_empty]

/-!
@concept regular_normal
@title Regular and Normal Spaces
@kind definition

Above Hausdorff the axioms stop separating points from points. They separate a point from a closed set, and then two closed sets from one another, which is what the deeper theorems of the subject need. Each is stated on top of T₁, and that is what keeps the hierarchy a chain.
-/

/-!
@problem define_regular_normal
@title The Definitions of Regular and Normal
@concept regular_normal

@preamble
The Hausdorff condition separates two points. Ask the same of a point and a closed set, and then of two closed sets, and two further axioms appear.

A space is *regular*, or T₃, when it is T₁ and every point outside a closed set has disjoint open sets separating it from that set. It is *normal*, or T₄, when it is T₁ and any two disjoint closed sets have disjoint open sets separating them.

Each carries T₁ as a conjunct, and without it the hierarchy would break: it is T₁ that makes a single point a closed set, and so makes the Hausdorff condition a case of regularity. Mathlib names these two `T3Space` and `T4Space`; what it calls `RegularSpace` and `NormalSpace` are the conditions with the T₁ left off.
@description
Define `TopologicalSpace.IsT3` and `TopologicalSpace.IsT4`, each a conjunction whose first half is `T.IsT1`. The second half of the first quantifies over `x : X` and `C : Set X` with `T.IsClosed C` and `x ∉ C`, and asks for `U` and `V` with `T.IsOpen U`, `T.IsOpen V`, `x ∈ U`, `C ⊆ V`, `U ∩ V = ∅`, in that order. The second quantifies over `C D : Set X`, both closed, with `C ∩ D = ∅`, and asks for `C ⊆ U` and `D ⊆ V` in the corresponding places.
-/

def TopologicalSpace.IsT3 {X : Type u} (T : TopologicalSpace X) : Prop :=
  T.IsT1 ∧ ∀ (x : X) (C : Set X), T.IsClosed C → x ∉ C →
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ C ⊆ V ∧ U ∩ V = ∅

def TopologicalSpace.IsT4 {X : Type u} (T : TopologicalSpace X) : Prop :=
  T.IsT1 ∧ ∀ C D : Set X, T.IsClosed C → T.IsClosed D → C ∩ D = ∅ →
    ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ C ⊆ U ∧ D ⊆ V ∧ U ∩ V = ∅

/-- @spec -/
example (X : Type) (T : TopologicalSpace X) :
    (T.IsT3 ↔ T.IsT1 ∧ ∀ (x : X) (C : Set X), T.IsClosed C → x ∉ C →
        ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ x ∈ U ∧ C ⊆ V ∧ U ∩ V = ∅)
      ∧ (T.IsT4 ↔ T.IsT1 ∧ ∀ C D : Set X, T.IsClosed C → T.IsClosed D → C ∩ D = ∅ →
        ∃ U V, T.IsOpen U ∧ T.IsOpen V ∧ C ⊆ U ∧ D ⊆ V ∧ U ∩ V = ∅) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! @end -/

/-!
@problem regular_normal_implications
@title Normal Implies Regular Implies Hausdorff
@concept regular_normal

@preamble
The chain closes, and T₁ is what closes it.

A normal space is regular. A point is a closed set, by the characterisation of T₁, and it is disjoint from any closed set it does not belong to — so normality applies to that pair and returns what regularity asks for.

A regular space is Hausdorff. Given `x ≠ y`, the set `{y}` is closed and `x` does not belong to it, so regularity separates `x` from `{y}`; an open set containing `{y}` contains `y`, which is the point the Hausdorff condition wanted separated.
@description
Prove `TopologicalSpace.isT3_of_isT4` and `TopologicalSpace.isT2_of_isT3`. Both apply `TopologicalSpace.isT1_iff_isClosed_singleton` to the first half of the hypothesis. For the first, `Set.eq_empty_of_forall_notMem` proves `{x} ∩ C = ∅`; in both, a containment `{x} ⊆ U` applied to `rfl` is the membership `x ∈ U`.
-/

theorem TopologicalSpace.isT3_of_isT4 {X : Type u} {T : TopologicalSpace X} (h : T.IsT4) :
    T.IsT3 := by
  refine ⟨h.1, fun x C hC hx => ?_⟩
  have hd : ({x} : Set X) ∩ C = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro z ⟨hz1, hz2⟩
    rw [show z = x from hz1] at hz2
    exact hx hz2
  obtain ⟨U, V, hU, hV, hxU, hCV, hUV⟩ :=
    h.2 {x} C ((TopologicalSpace.isT1_iff_isClosed_singleton T).mp h.1 x) hC hd
  exact ⟨U, V, hU, hV, hxU rfl, hCV, hUV⟩

theorem TopologicalSpace.isT2_of_isT3 {X : Type u} {T : TopologicalSpace X} (h : T.IsT3) :
    T.IsT2 := by
  intro x y hxy
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ :=
    h.2 x {y} ((TopologicalSpace.isT1_iff_isClosed_singleton T).mp h.1 y) hxy
  exact ⟨U, V, hU, hV, hxU, hyV rfl, hUV⟩

/-! @end -/

/--
@problem discrete_normal
@title A Discrete Space is Normal
@concept regular_normal

@preamble
Where every subset is open there is nothing to arrange. Two disjoint closed sets are already two disjoint open sets, and each separates the other; the T₁ half is as cheap, since the complement of a point is open like everything else.

So the discrete topology satisfies all five axioms, and the indiscrete one fails the first. The two extremes bound the hierarchy as they bound everything else built from open sets.
@description
Show that `(discrete X).IsT4`. For the T₁ half offer `{y}ᶜ`; for the second half offer the two closed sets unchanged, with `subset_rfl` for the two containments and the hypothesis for the disjointness. Openness in the discrete topology is `trivial`.
-/
theorem discrete_isT4 (X : Type u) : (discrete X).IsT4 := by
  constructor
  · intro x y hxy
    exact ⟨{y}ᶜ, trivial, hxy, fun hn => hn rfl⟩
  · intro C D _ _ hCD
    exact ⟨C, D, trivial, trivial, subset_rfl, subset_rfl, hCD⟩

/--
@problem metric_regular
@title Every Metric Space is Regular
@concept regular_normal

@preamble
Let `C` be closed and let `x` lie outside it. Then `x` belongs to the open set `Cᶜ`, so some ball `M.ball x ε` misses `C` altogether.

Halve that radius. Around `x` put `M.ball x (ε / 2)`; around `C` put the union of the balls `M.ball c (ε / 2)` taken over the points `c` of `C`. The second is open, being a union of balls, and it covers `C`, each point of `C` being the centre of one of them.

The two do not meet. A point `z` in both is within `ε / 2` of `x` and within `ε / 2` of some `c` of `C`, so `x` is within `ε` of `c` — and no point of `C` is that close to `x`.
@description
Show that `M.toTopologicalSpace.IsT3`. The T₁ half is the Hausdorff problem read through the implications. Write the union as `⋃₀ {B | ∃ c ∈ C, B = M.ball c (ε / 2)}`, whose openness is `MetricSpace.isOpenSet_sUnion` once a member is taken apart by `rintro B ⟨c, _, rfl⟩`; `M.dist_triangle x z c` and `M.dist_comm` then feed `linarith`.
-/
theorem MetricSpace.isT3 {X : Type u} (M : MetricSpace X) : M.toTopologicalSpace.IsT3 := by
  refine ⟨TopologicalSpace.isT1_of_isT2 (MetricSpace.isT2 M), fun x C hC hx => ?_⟩
  obtain ⟨ε, hε, hball⟩ := hC x hx
  have hopen : M.IsOpenSet (⋃₀ {B | ∃ c ∈ C, B = M.ball c (ε / 2)}) :=
    MetricSpace.isOpenSet_sUnion M (by rintro B ⟨c, _, rfl⟩; exact MetricSpace.isOpenSet_ball M c _)
  have hCV : C ⊆ ⋃₀ {B | ∃ c ∈ C, B = M.ball c (ε / 2)} :=
    fun c hc => ⟨M.ball c (ε / 2), ⟨c, hc, rfl⟩, MetricSpace.mem_ball_self M c _ (by linarith)⟩
  refine ⟨M.ball x (ε / 2), _, MetricSpace.isOpenSet_ball M x _, hopen,
    MetricSpace.mem_ball_self M x _ (by linarith), hCV, ?_⟩
  apply Set.eq_empty_of_forall_notMem
  rintro z ⟨hz1, B, ⟨c, hc, rfl⟩, hz2⟩
  rw [MetricSpace.mem_ball M] at hz1 hz2
  have e : M.dist c z = M.dist z c := M.dist_comm
  have ht := M.dist_triangle x z c
  exact hball ((MetricSpace.mem_ball M).mpr (by linarith)) hc

end GeneralTopology
