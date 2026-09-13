import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.MetricSpaces

/-! @section Topological Spaces -/

universe u

namespace GeneralTopology

/-!
@concept open_sets
@title The Open Sets of a Metric Space
@kind definition

A metric answers how far apart two points are, but most of what is built on it asks only a coarser question: is there room around this point? A set with room around each of its points is called open. Which sets are open turns out to be all that the later notions use, and it is the bridge from measuring to the subject proper.
-/

/-!
@problem define_is_open_set
@title Open Sets
@concept open_sets

@preamble
A subset `U` of a metric space is *open* when every point of it has room to spare: for each `x` in `U` there is a radius `ε > 0`, however small, with the whole ball `M.ball x ε` inside `U`. No point of an open set sits on its edge.

The radius depends on the point, and that is the whole content of the definition. A point deep inside `U` has a generous ball; one near the edge has a small one; what is asked is only that some positive radius works for each.

`∃ ε > 0, p ε` abbreviates `∃ ε, ε > 0 ∧ p ε`.
@description
Define `Metric.IsOpenSet`, which says that `U` is open in the metric space `M`: for every `x` in `U` there is a positive `ε` with `M.ball x ε ⊆ U`.
-/

def Metric.IsOpenSet {X : Type u} (M : Metric X) (U : Set X) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, M.ball x ε ⊆ U

/-- @spec -/
example (X : Type) (M : Metric X) (U : Set X) :
    M.IsOpenSet U ↔ ∀ x ∈ U, ∃ ε > 0, M.ball x ε ⊆ U := Iff.rfl

/-! @end -/

/--
@problem ball_is_open
@title An Open Ball is an Open Set
@concept open_sets

@preamble
The name would be a poor one if a ball were not open, so this is the first thing to check.

Let `y` be a point of `M.ball x ε`, so `M.dist x y < ε`. The room left over is exactly `ε - M.dist x y`, and it is positive. A point `z` within that of `y` is within `ε` of `x`, since the trip from `x` to `z` may be made through `y`: `M.dist x z ≤ M.dist x y + M.dist y z < M.dist x y + (ε - M.dist x y)`.
@description
Show that `M.ball x ε` is open. Introduce a point of it and rewrite its membership as the inequality it is, offer `ε - M.dist x y` as the radius, and let the triangle inequality and `linarith` do the rest.
-/
theorem Metric.isOpenSet_ball {X : Type u} (M : Metric X) (x : X) (ε : ℝ) :
    M.IsOpenSet (M.ball x ε) := by
  intro y hy
  rw [M.mem_ball] at hy
  refine ⟨ε - M.dist x y, by linarith, ?_⟩
  intro z hz
  rw [M.mem_ball] at hz ⊢
  have h := M.triangle x y z
  linarith

/--
@problem is_open_set_univ
@title The Whole Space is Open
@concept open_sets

@preamble
Every point of the whole space has room around it, since every ball is inside the whole space whatever its radius. Any positive number will serve; `1` is as good as another.
@description
Show that `Set.univ` is open in any metric space. The witness is `⟨1, one_pos, _⟩`, and the containment holds because everything belongs to `Set.univ`, which `trivial` proves.
-/
theorem Metric.isOpenSet_univ {X : Type u} (M : Metric X) : M.IsOpenSet (Set.univ : Set X) :=
  fun _ _ => ⟨1, one_pos, fun _ _ => trivial⟩

/--
@problem is_open_set_inter
@title The Intersection of Two Open Sets
@concept open_sets

@preamble
A point of `U ∩ V` has room inside `U` and room inside `V` — two radii, one from each. The smaller of the two serves for both, and it is still positive.

This is where *two* matters. For infinitely many open sets the radii could shrink towards zero with no positive number below them all, and the intersection need not be open.
@description
Show that `U ∩ V` is open when `U` and `V` are. Take a point apart with `hx.1` and `hx.2`, take each hypothesis apart with `obtain`, and offer `min a b`, which `lt_min` shows positive; `min_le_left` and `min_le_right` then carry a point of the smaller ball into each of the two.
-/
theorem Metric.isOpenSet_inter {X : Type u} (M : Metric X) {U V : Set X}
    (hU : M.IsOpenSet U) (hV : M.IsOpenSet V) : M.IsOpenSet (U ∩ V) := by
  intro x hx
  obtain ⟨a, ha, hau⟩ := hU x hx.1
  obtain ⟨b, hb, hbv⟩ := hV x hx.2
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro y hy
  rw [M.mem_ball] at hy
  exact ⟨hau (lt_of_lt_of_le hy (min_le_left a b)), hbv (lt_of_lt_of_le hy (min_le_right a b))⟩

/--
@problem is_open_set_union
@title A Union of Open Sets, However Many
@concept open_sets

@preamble
Here the number of sets does not matter at all. A point of the union lies in one of them, that one is open, so it supplies a ball around the point — and the ball, being inside that one set, is inside the union.

A collection of sets is itself a set: `F : Set (Set X)`. Its union is `⋃₀ F`, the points belonging to at least one member, and `x ∈ ⋃₀ F` unfolds to `∃ U, U ∈ F ∧ x ∈ U`.
@description
Show that `⋃₀ F` is open when every member of `F` is. Take the membership apart for the set the point came from, get a ball from that set's openness, and offer the same ball; a point of it lies in that member, hence in the union.
-/
theorem Metric.isOpenSet_sUnion {X : Type u} (M : Metric X) {F : Set (Set X)}
    (h : ∀ U ∈ F, M.IsOpenSet U) : M.IsOpenSet (⋃₀ F) := by
  intro x hx
  obtain ⟨U, hUF, hxU⟩ := hx
  obtain ⟨ε, hε, hsub⟩ := h U hUF x hxU
  exact ⟨ε, hε, fun y hy => ⟨U, hUF, hsub hy⟩⟩

/-!
@concept topological_space
@title Topological Spaces
@kind definition

The three facts just proved are all that most of the subject uses about a metric. So take them as the definition: a topology on a set is a choice of which subsets are open, asked only to contain the whole set and to be closed under intersecting two and uniting any number. What is gained is everything that has open sets but no distance.
-/

/-!
@problem define_topology
@title The Definition of a Topological Space
@concept topological_space

@preamble
A *topology* on a set `X` names some of its subsets open, subject to three conditions — the three facts that were just proved about a metric space, and nothing more.

The whole set is open. The intersection of two open sets is open. The union of any collection of open sets is open, the collection being a `Set (Set X)` and the union `⋃₀ F`.

Two and any number are not the same condition, and the asymmetry is the point: intersecting needs a smallest radius, and only finitely many radii are sure to have one.
@description
Define the structure `Topology X`, with a field `IsOpen : Set X → Prop` and then `univ`, `inter` and `sUnion` carrying the three conditions. Bind the sets implicitly in `inter` and `sUnion`, since a proof using them names the hypotheses rather than the sets.
-/

structure Topology (X : Type u) where
  IsOpen : Set X → Prop
  univ : IsOpen Set.univ
  inter : ∀ {U V}, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  sUnion : ∀ {F : Set (Set X)}, (∀ U ∈ F, IsOpen U) → IsOpen (⋃₀ F)

/-- @spec -/
example (X : Type) (T : Topology X) (U V : Set X) (F : Set (Set X)) :
    T.IsOpen Set.univ
      ∧ (T.IsOpen U → T.IsOpen V → T.IsOpen (U ∩ V))
      ∧ ((∀ W ∈ F, T.IsOpen W) → T.IsOpen (⋃₀ F)) := by
  refine ⟨T.univ, fun _ _ => ?_, fun _ => ?_⟩
  · apply T.inter <;> assumption
  · apply T.sUnion
    assumption

/-! @end -/

/--
@problem empty_is_open
@title The Empty Set is Open
@concept topological_space

@preamble
The empty set was not asked for, and does not need to be: it is the union of no sets at all. Uniting the members of the empty collection leaves nothing, so `⋃₀ ∅ = ∅`, and the union condition applies to the empty collection as to any other — its hypothesis, that every member is open, is satisfied because it has no members.
@description
Show that `∅` is open in any topology. Apply `T.sUnion` to the empty collection, whose hypothesis holds because a membership in `∅` is absurd — `fun _ hU => hU.elim` — and then rewrite with `Set.sUnion_empty`.
-/
theorem Topology.empty {X : Type u} (T : Topology X) : T.IsOpen (∅ : Set X) := by
  have h : T.IsOpen (⋃₀ (∅ : Set (Set X))) := T.sUnion (fun _ hU => hU.elim)
  rwa [Set.sUnion_empty] at h

/-!
@concept metric_topology
@title The Topology of a Metric
@kind theorem

Every metric space is a topological space, by taking the open sets to be the ones the metric already calls open. This is the reason the axioms were chosen as they were, and it is the source of most of the examples: whenever a set carries a distance it carries a topology, and different distances may well give the same one.
-/

/-!
@problem define_metric_topology
@title Every Metric Space is a Topological Space
@concept metric_topology

@preamble
Nothing is left to prove. The three conditions are the three theorems of the first concept, so the construction is a matter of naming them in the right fields.

That a metric gives a topology is what makes the definition worth having; that two metrics can give the same one is what makes it more than a restatement. The taxicab and supremum norms of the previous section are an instance — equivalent metrics, and the same open sets.
@description
Define `Metric.toTopology`, the topology whose open sets are the sets `M` calls open. Each field is one of `M.isOpenSet_univ`, `M.isOpenSet_inter` and `M.isOpenSet_sUnion`.
-/

def Metric.toTopology {X : Type u} (M : Metric X) : Topology X where
  IsOpen := M.IsOpenSet
  univ := M.isOpenSet_univ
  inter := M.isOpenSet_inter
  sUnion := M.isOpenSet_sUnion

/-- @spec -/
example (X : Type) (M : Metric X) (U : Set X) : M.toTopology.IsOpen U ↔ M.IsOpenSet U := Iff.rfl

/-! @end -/

/-!
@concept closed_sets
@title Closed Sets
@kind definition

A set is closed when its complement is open. Closed is not the opposite of open and not its negation: a set may be both, as the whole space is, or neither. The two notions carry the same information — each determines the other — and which is more convenient depends on what is being said.
-/

/-!
@problem define_is_closed
@title The Definition of a Closed Set
@concept closed_sets

@preamble
A subset `C` of a topological space is *closed* when its complement `Cᶜ` is open. Nothing else is required, and nothing else is meant: closed is a name for a property of the complement.

Since the whole space is open, the empty set is closed; since the empty set is open, the whole space is closed. Both are therefore open and closed at once, which is why "closed" must not be read as "not open".
@description
Define `Topology.IsClosed`, and then show that `Set.univ` is closed. For the second, `show T.IsOpen _` names the goal for what it is, `Set.compl_univ` rewrites the complement, and the empty set is open.
-/

def Topology.IsClosed {X : Type u} (T : Topology X) (C : Set X) : Prop := T.IsOpen Cᶜ

theorem Topology.isClosed_univ {X : Type u} (T : Topology X) : T.IsClosed (Set.univ : Set X) := by
  show T.IsOpen _
  rw [Set.compl_univ]
  exact T.empty

/-- @spec -/
example (X : Type) (T : Topology X) (C : Set X) : T.IsClosed C ↔ T.IsOpen Cᶜ := Iff.rfl

/-! @end -/

/--
@problem is_closed_union
@title The Union of Two Closed Sets
@concept closed_sets

@preamble
Each condition on the open sets says something about the closed ones, with the roles of union and intersection exchanged, because complementing exchanges them: `(C ∪ D)ᶜ = Cᶜ ∩ Dᶜ`. So the union of two closed sets is closed, matching the intersection of two open ones, and — though it is not proved here — an intersection of any number of closed sets is closed.
@description
Show that `C ∪ D` is closed when `C` and `D` are. `show T.IsOpen _`, rewrite with `Set.compl_union`, and the intersection condition finishes it.
-/
theorem Topology.isClosed_union {X : Type u} (T : Topology X) {C D : Set X}
    (hC : T.IsClosed C) (hD : T.IsClosed D) : T.IsClosed (C ∪ D) := by
  show T.IsOpen _
  rw [Set.compl_union]
  exact T.inter hC hD

/-!
@concept neighbourhoods
@title Neighbourhoods
@kind definition

A neighbourhood of a point is any set with an open set around that point inside it. The notion localises openness: a set is open exactly when it is a neighbourhood of each of its own points. That equivalence is how a global condition on a set is traded for a condition at each point, which is the form nearly every later argument takes.
-/

/-!
@problem define_nbhd
@title The Definition of a Neighbourhood
@concept neighbourhoods

@preamble
A set `N` is a *neighbourhood* of a point `x` when some open set `U` has `x ∈ U ⊆ N`. A neighbourhood need not itself be open — it must only contain an open set around the point — and an open set is a neighbourhood of each of its own points, itself being the `U` required.
@description
Define `Topology.IsNbhd`, and then show that an open set is a neighbourhood of any of its points. The witness for the second is the set itself, with `subset_rfl` for the containment.
-/

def Topology.IsNbhd {X : Type u} (T : Topology X) (x : X) (N : Set X) : Prop :=
  ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ⊆ N

theorem Topology.nbhd_of_isOpen {X : Type u} (T : Topology X) {U : Set X}
    (hU : T.IsOpen U) {x : X} (hx : x ∈ U) : T.IsNbhd x U :=
  ⟨U, hU, hx, subset_rfl⟩

/-- @spec -/
example (X : Type) (T : Topology X) (x : X) (N : Set X) :
    T.IsNbhd x N ↔ ∃ U, T.IsOpen U ∧ x ∈ U ∧ U ⊆ N := Iff.rfl

/-! @end -/

/--
@problem union_of_opens_inside
@title A Set is the Union of the Open Sets Inside It
@concept neighbourhoods

@preamble
Suppose every point of `U` has an open set around it inside `U`. Collect all the open sets contained in `U`: their union is contained in `U`, since each of them is, and it contains every point of `U`, since each point has one of them around it. So `U` is that union exactly.

This is the step that turns a condition holding at each point into a single set built by the union rule.
@description
Show that `U = ⋃₀ {V | T.IsOpen V ∧ V ⊆ U}` under that hypothesis. `Set.Subset.antisymm` splits the equality into the two containments; one takes the open set the hypothesis supplies, and the other reads the membership apart with `rintro` and applies the containment it carries.
-/
theorem Topology.union_of_opens_inside {X : Type u} (T : Topology X) (U : Set X)
    (h : ∀ x ∈ U, T.IsNbhd x U) : U = ⋃₀ {V | T.IsOpen V ∧ V ⊆ U} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := h x hx
    exact ⟨V, ⟨hV, hVU⟩, hxV⟩
  · rintro x ⟨V, ⟨_, hVU⟩, hxV⟩
    exact hVU hxV

/--
@problem is_open_iff_nbhd
@title Open Means a Neighbourhood of Each of Its Points
@concept neighbourhoods

@preamble
Now the two directions meet. An open set is a neighbourhood of each of its points, being itself the open set required. And a set that is a neighbourhood of each of its points is the union of the open sets inside it, which the union condition makes open.

So openness, a property of a set, is exactly a property holding at every one of its points. Every later notion in topology is stated in the second form.
@description
Prove the equivalence. The forward direction is the previous concept's `T.nbhd_of_isOpen`; for the other, rewrite `U` by the previous problem and apply the union condition, whose hypothesis is the first half of each member's defining pair.
-/
theorem Topology.isOpen_iff_nbhd {X : Type u} (T : Topology X) (U : Set X) :
    T.IsOpen U ↔ ∀ x ∈ U, T.IsNbhd x U := by
  constructor
  · intro hU x hx
    exact T.nbhd_of_isOpen hU hx
  · intro h
    rw [T.union_of_opens_inside U h]
    exact T.sUnion (fun V hV => hV.1)

end GeneralTopology
