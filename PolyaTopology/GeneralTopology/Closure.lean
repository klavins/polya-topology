import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.TopologicalSpaces

/-! @section Closure, Interior and Boundary -/

universe u

namespace GeneralTopology

/-!
@concept closed_families
@title Families of Closed Sets
@kind theorem

Every condition on the open sets has a mirror image about the closed ones, with union and intersection exchanged, because complementing exchanges them. The last section took one of those mirrors and left two. Both are needed here, and the first of them is what the next concept is built out of.
-/

/--
@problem is_closed_empty
@title The Empty Set is Closed
@concept closed_families

@preamble
The whole space is closed because the empty set is open. The dual is as short: the empty set is closed because its complement is the whole space, which every topology calls open.
@description
Show that `∅` is closed in any topology. `show T.IsOpen _` names the goal for what it is, `Set.compl_empty` rewrites the complement, and the whole space is open.
-/
theorem Topology.isClosed_empty {X : Type u} (T : Topology X) : T.IsClosed (∅ : Set X) := by
  show T.IsOpen _
  rw [Set.compl_empty]
  exact T.univ

/--
@problem is_closed_intersection
@title An Intersection of Closed Sets, However Many
@concept closed_families

@preamble
The union condition on open sets says that a union of any number of them is open. Its mirror says that an intersection of any number of closed sets is closed, and the proof is the union condition read through a complement.

Complementing an intersection gives the union of the complements. Mathlib writes the collection of complements as `compl '' F`, the image of `F` under complementation, and `Set.compl_sInter` is the equation `(⋂₀ F)ᶜ = ⋃₀ (compl '' F)`. A member of an image arrives with the member it came from.
@description
Show that `⋂₀ F` is closed when every member of `F` is. `show T.IsOpen _`, rewrite with `Set.compl_sInter`, and apply the union condition; its hypothesis takes a member of the image, which `rintro U ⟨C, hCF, rfl⟩` breaks into the set `C` it came from.
-/
theorem Topology.isClosed_sInter {X : Type u} (T : Topology X) {F : Set (Set X)}
    (h : ∀ C ∈ F, T.IsClosed C) : T.IsClosed (⋂₀ F) := by
  show T.IsOpen _
  rw [Set.compl_sInter]
  apply T.sUnion
  rintro U ⟨C, hCF, rfl⟩
  exact h C hCF

/-!
@concept closure
@title The Closure of a Set
@kind definition

An arbitrary set is neither open nor closed, and the topology's first act on it is to close it: to name the smallest closed set it cannot escape. That set is its closure, and it exists because closed sets are stable under intersecting any number of them. It is what the topology makes of a set it was not given.
-/

/-!
@problem define_closure
@title The Definition of the Closure
@concept closure

@preamble
Let `S` be any subset of a topological space. Some closed sets contain `S` — the whole space, at worst — so we may intersect all of them at once. What comes out is closed, by the problem above; it contains `S`, because each set intersected does; and it is inside every closed set containing `S`, because an intersection is inside each of its members.

That is the *closure* of `S`, written `T.closure S`: the smallest closed set containing `S`. The collection to intersect is a `Set (Set X)`, its intersection is `⋂₀`, and membership in `⋂₀ F` unfolds to `∀ C ∈ F, x ∈ C`.
@description
Define `Topology.closure`, which takes a topology `T` on `X` and a set `S` and returns the intersection of every closed set containing `S`. The collection to intersect is `{C | T.IsClosed C ∧ S ⊆ C}`.
-/

def Topology.closure {X : Type u} (T : Topology X) (S : Set X) : Set X :=
  ⋂₀ {C | T.IsClosed C ∧ S ⊆ C}

/-- @spec -/
example (X : Type) (T : Topology X) (S : Set X) (x : X) :
    x ∈ T.closure S ↔ ∀ C, T.IsClosed C ∧ S ⊆ C → x ∈ C := Iff.rfl

/-! @end -/

/-!
@problem closure_smallest
@title The Closure is the Smallest Closed Set Containing S
@concept closure

@preamble
Three properties say everything the closure is, and each is a line of the definition read back.

It contains `S`: a point of `S` belongs to every closed set containing `S`, hence to their intersection. It is closed: an intersection of closed sets is closed, and every member of this collection was chosen closed. And it is the smallest: if `C` is closed and contains `S`, then `C` is one of the sets intersected, so the intersection is inside it.

The third is the one that does the work later. Every fact about a closure below is proved by naming a closed set that contains `S`.
@description
Prove the three. For each, a membership in `⋂₀` is a function: `hx C hC` is the proof that `x` lies in `C`, given `hC` that `C` belongs to the collection, and `hC.1` and `hC.2` are its two halves.
-/

theorem Topology.subset_closure {X : Type u} (T : Topology X) (S : Set X) : S ⊆ T.closure S := by
  intro x hx C hC
  exact hC.2 hx

theorem Topology.isClosed_closure {X : Type u} (T : Topology X) (S : Set X) :
    T.IsClosed (T.closure S) :=
  T.isClosed_sInter (fun _ hC => hC.1)

theorem Topology.closure_min {X : Type u} (T : Topology X) {S C : Set X}
    (hC : T.IsClosed C) (hSC : S ⊆ C) : T.closure S ⊆ C := by
  intro x hx
  exact hx C ⟨hC, hSC⟩

/-! @end -/

/--
@problem is_closed_iff_closure_eq
@title A Set is Closed Exactly When it is its Own Closure
@concept closure

@preamble
The closure adds to `S` whatever is needed to make it closed, so it adds nothing exactly when `S` was closed already.

One direction: if `S` is closed then `S` is a closed set containing `S`, so the closure is inside `S`, and `S` is inside the closure, so the two are equal. The other: if the closure equals `S` then `S` is closed, the closure being closed whatever `S` is.
@description
Prove that `T.IsClosed S` exactly when `T.closure S = S`. `Set.Subset.antisymm` builds the equality from the two containments, and `subset_rfl` says a set contains itself; for the converse, rewrite backwards along the hypothesis.
-/
theorem Topology.isClosed_iff_closure_eq {X : Type u} (T : Topology X) (S : Set X) :
    T.IsClosed S ↔ T.closure S = S := by
  constructor
  · intro hS
    exact Set.Subset.antisymm (T.closure_min hS subset_rfl) (T.subset_closure S)
  · intro h
    rw [← h]
    exact T.isClosed_closure S

/-!
@problem closure_mono_idem
@title The Closure is Monotone and Idempotent
@concept closure

@preamble
Two properties that any operation deserving the name of a closure has.

*Monotone*: a larger set has a larger closure. If `S ⊆ S'` then the closure of `S'` is a closed set containing `S`, so it contains the closure of `S`.

*Idempotent*: closing twice is closing once. The closure of `S` is closed, and a closed set is its own closure.
@description
Prove the two. Both are one application of a fact already proved: the first of `T.closure_min`, with `Set.Subset.trans` — written `h.trans` — to see that the larger closure contains `S`; the second of the equivalence above, in its left-to-right direction.
-/

theorem Topology.closure_mono {X : Type u} (T : Topology X) {S S' : Set X} (h : S ⊆ S') :
    T.closure S ⊆ T.closure S' :=
  T.closure_min (T.isClosed_closure S') (h.trans (T.subset_closure S'))

theorem Topology.closure_closure {X : Type u} (T : Topology X) (S : Set X) :
    T.closure (T.closure S) = T.closure S :=
  (T.isClosed_iff_closure_eq (T.closure S)).mp (T.isClosed_closure S)

/-! @end -/

/--
@problem closure_union
@title The Closure of a Union of Two Sets
@concept closure

@preamble
Closing a union of two sets is the same as closing each and uniting. This is the first statement about closures that is not a restatement of the definition, and it is proved entirely from the three properties above.

One containment is monotonicity twice, since each set is inside the union. For the other, `T.closure S ∪ T.closure S'` is a closed set — a union of two closed sets is closed — and it contains `S ∪ S'`, so it contains the closure of the union.

Two is essential. For infinitely many sets the union of the closures need not be closed, and the statement fails.
@description
Prove that `T.closure (S ∪ S') = T.closure S ∪ T.closure S'`. Split with `Set.Subset.antisymm`; `Set.union_subset_union` and `Set.union_subset` combine two containments into one, and `Set.subset_union_left` and `Set.subset_union_right` put a set inside a union.
-/
theorem Topology.closure_union {X : Type u} (T : Topology X) (S S' : Set X) :
    T.closure (S ∪ S') = T.closure S ∪ T.closure S' := by
  apply Set.Subset.antisymm
  · apply T.closure_min (T.isClosed_union (T.isClosed_closure S) (T.isClosed_closure S'))
    exact Set.union_subset_union (T.subset_closure S) (T.subset_closure S')
  · exact Set.union_subset (T.closure_mono Set.subset_union_left)
      (T.closure_mono Set.subset_union_right)

/-!
@concept closure_points
@title The Points of the Closure
@kind theorem

The closure was built from outside, by intersecting the closed sets around a set. It has a description from inside: a point belongs to it exactly when the set is found arbitrarily near. That is the form every later use takes, and in a metric space it becomes a statement about balls, which is how a limit will be defined.
-/

/--
@problem mem_closure_iff
@title A Point of the Closure is Approached by the Set
@concept closure_points

@preamble
Which points does closing add? Exactly those that `S` comes arbitrarily close to: `x` lies in `T.closure S` when no neighbourhood of `x` avoids `S`.

Suppose some neighbourhood `N` of `x` misses `S`, and let `U` be the open set with `x ∈ U ⊆ N`. Then `U` misses `S` too, so `Uᶜ` is a closed set containing `S`; the closure lies inside it, and `x` does not.

Conversely, suppose `x` escapes some closed `C` containing `S`. Then `Cᶜ` is open and holds `x`, so it is a neighbourhood of `x`, and it misses `S` because `S` is inside `C`.
@description
Prove that `x ∈ T.closure S` exactly when every neighbourhood `N` of `x` meets `S` — written `(N ∩ S).Nonempty`, a point in both. Each direction assumes the opposite of what it wants and derives `False`, which is what `by_contra` sets up.
-/
theorem Topology.mem_closure_iff {X : Type u} (T : Topology X) {S : Set X} {x : X} :
    x ∈ T.closure S ↔ ∀ N, T.IsNbhd x N → (N ∩ S).Nonempty := by
  constructor
  · rintro hx N ⟨U, hU, hxU, hUN⟩
    by_contra h
    have hSU : S ⊆ Uᶜ := by
      intro y hy hyU
      exact h ⟨y, hUN hyU, hy⟩
    have hcl : T.IsClosed Uᶜ := by
      show T.IsOpen _
      rwa [compl_compl]
    exact hx Uᶜ ⟨hcl, hSU⟩ hxU
  · intro h C hC
    by_contra hxC
    obtain ⟨y, hyC, hyS⟩ := h Cᶜ ⟨Cᶜ, hC.1, hxC, subset_rfl⟩
    exact hyC (hC.2 hyS)

/--
@problem metric_mem_closure_iff
@title The Closure in a Metric Space
@concept closure_points

@preamble
In a metric space the neighbourhoods of `x` are exactly the sets holding a ball about `x`, so the condition above is a condition on balls: `x` lies in the closure of `S` when every ball about `x`, however small, contains a point of `S`.

One direction is the previous problem applied to a ball, which is a neighbourhood of its centre because a ball is open and holds its centre. The other takes a neighbourhood, extracts from its open set a ball about `x` inside it, and finds the point of `S` there.
@description
Prove that `x ∈ M.toTopology.closure S` exactly when `(M.ball x ε ∩ S).Nonempty` for every `ε > 0`. Begin by rewriting with the previous problem; `M.toTopology.nbhd_of_isOpen`, `M.isOpenSet_ball` and `M.mem_ball_self` supply the neighbourhood, and openness of the neighbourhood's open set supplies the ball.
-/
theorem Metric.mem_closure_iff {X : Type u} (M : Metric X) {S : Set X} {x : X} :
    x ∈ M.toTopology.closure S ↔ ∀ ε > 0, (M.ball x ε ∩ S).Nonempty := by
  rw [M.toTopology.mem_closure_iff]
  constructor
  · intro h ε hε
    have hN : M.toTopology.IsNbhd x (M.ball x ε) :=
      M.toTopology.nbhd_of_isOpen (M.isOpenSet_ball x ε) (M.mem_ball_self x ε hε)
    exact h (M.ball x ε) hN
  · rintro h N ⟨U, hU, hxU, hUN⟩
    obtain ⟨ε, hε, hball⟩ := hU x hxU
    obtain ⟨y, hy, hyS⟩ := h ε hε
    exact ⟨y, hUN (hball hy), hyS⟩

/-!
@concept interior_boundary
@title Interior and Boundary
@kind definition

Dual to the closure, and built the same way from the other end: the largest open set inside a set. The interior holds the points with room around them, the closure the points the set approaches, and what lies between the two is the boundary. A set is open and closed at once exactly when that is empty.
-/

/-!
@problem define_interior
@title The Definition of the Interior
@concept interior_boundary

@preamble
The closure was built by intersecting from outside. The interior is built by uniting from inside: some open sets are contained in `S` — the empty one, at worst — so unite all of them. What comes out is open, by the union condition; it is inside `S`, because each set united is; and it contains every open subset of `S`, because a union contains each of its members.

That is the *interior* of `S`, written `T.interior S`. Membership in `⋃₀ F` unfolds to `∃ U, U ∈ F ∧ x ∈ U`.
@description
Define `Topology.interior`, which takes a topology `T` on `X` and a set `S` and returns the union of every open set contained in `S`. The collection to unite is `{U | T.IsOpen U ∧ U ⊆ S}`.
-/

def Topology.interior {X : Type u} (T : Topology X) (S : Set X) : Set X :=
  ⋃₀ {U | T.IsOpen U ∧ U ⊆ S}

/-- @spec -/
example (X : Type) (T : Topology X) (S : Set X) (x : X) :
    x ∈ T.interior S ↔ ∃ U, (T.IsOpen U ∧ U ⊆ S) ∧ x ∈ U := Iff.rfl

/-! @end -/

/-!
@problem interior_largest
@title The Interior is the Largest Open Set Inside S
@concept interior_boundary

@preamble
Three properties, mirroring the three that characterised the closure, and proved the same way: each is a line of the definition read back.

The interior is open, by the union condition applied to a collection whose members were all chosen open. It is contained in `S`, because each member is. And it contains every open `U` inside `S`, because such a `U` is one of the sets united.
@description
Prove the three. A membership in `⋃₀` is a triple: the set it came from, the proof that set belongs to the collection, and the proof the point lies in it. `rintro x ⟨U, ⟨_, hUS⟩, hxU⟩` takes one apart, and an anonymous constructor builds one.
-/

theorem Topology.isOpen_interior {X : Type u} (T : Topology X) (S : Set X) :
    T.IsOpen (T.interior S) :=
  T.sUnion (fun _ hU => hU.1)

theorem Topology.interior_subset {X : Type u} (T : Topology X) (S : Set X) :
    T.interior S ⊆ S := by
  rintro x ⟨U, ⟨_, hUS⟩, hxU⟩
  exact hUS hxU

theorem Topology.interior_max {X : Type u} (T : Topology X) {U S : Set X}
    (hU : T.IsOpen U) (hUS : U ⊆ S) : U ⊆ T.interior S :=
  fun _ hx => ⟨U, ⟨hU, hUS⟩, hx⟩

/-! @end -/

/--
@problem is_open_iff_interior_eq
@title A Set is Open Exactly When it is its Own Interior
@concept interior_boundary

@preamble
The mirror of the closure's equivalence, and one direction of it is already proved. The last section showed that a set which is a neighbourhood of each of its points is the union of the open sets inside it — which is to say, its own interior. An open set is such a set.

The converse is the easier half: if `S` equals its interior then `S` is open, the interior being open whatever `S` is.
@description
Prove that `T.IsOpen S` exactly when `T.interior S = S`. For the forward direction, `T.isOpen_iff_nbhd` turns openness into the hypothesis that `T.union_of_opens_inside` wants, and the equation it returns is this one reversed.
-/
theorem Topology.isOpen_iff_interior_eq {X : Type u} (T : Topology X) (S : Set X) :
    T.IsOpen S ↔ T.interior S = S := by
  constructor
  · intro hS
    exact (T.union_of_opens_inside S ((T.isOpen_iff_nbhd S).mp hS)).symm
  · intro h
    rw [← h]
    exact T.isOpen_interior S

/--
@problem compl_closure
@title Closure and Interior are Complements of Each Other
@concept interior_boundary

@preamble
The two operations are one operation seen from the two sides. Complementing turns closed into open, containment around, and the smallest into the largest — so the complement of the closure of `S` is the interior of the complement of `S`.

Each containment is one of the two universal properties. The complement of the closure is open, since the closure is closed, and it lies inside `Sᶜ`, since `S` lies inside its closure; so it lies inside the interior of `Sᶜ`. And the complement of the interior of `Sᶜ` is closed and contains `S`, so it contains the closure of `S`, which is the other containment complemented.
@description
Prove that `(T.closure S)ᶜ = T.interior Sᶜ`. `Set.subset_compl_comm` moves a complement from one side of a containment to the other, `Set.compl_subset_compl` reverses one under complementing, and `compl_compl` cancels two.
-/
theorem Topology.compl_closure {X : Type u} (T : Topology X) (S : Set X) :
    (T.closure S)ᶜ = T.interior Sᶜ := by
  apply Set.Subset.antisymm
  · apply T.interior_max (T.isClosed_closure S)
    exact Set.compl_subset_compl.mpr (T.subset_closure S)
  · rw [Set.subset_compl_comm]
    apply T.closure_min
    · show T.IsOpen _
      rw [compl_compl]
      exact T.isOpen_interior Sᶜ
    · rw [Set.subset_compl_comm]
      exact T.interior_subset Sᶜ

/-!
@problem define_boundary
@title The Definition of the Boundary
@concept interior_boundary

@preamble
The interior of `S` is inside `S`, and `S` is inside its closure, so the three sit in a line. What the closure has and the interior has not is the *boundary* of `S`, written `T.boundary S`: the points approached by `S` and by its complement alike, with room around them in neither.

On the line, the boundary of an interval is its two endpoints, whether or not the interval contains them.
@description
Define `Topology.boundary` as the closure of `S` with the interior taken away. Lean writes the difference of two sets with a backslash, `A \ B`, and a membership in it is a pair: in `A`, and not in `B`.
-/

def Topology.boundary {X : Type u} (T : Topology X) (S : Set X) : Set X :=
  T.closure S \ T.interior S

/-- @spec -/
example (X : Type) (T : Topology X) (S : Set X) (x : X) :
    x ∈ T.boundary S ↔ (x ∈ T.closure S ∧ x ∉ T.interior S) := Iff.rfl

/-! @end -/

/--
@problem boundary_eq_empty_iff
@title A Set With No Boundary is Open and Closed
@concept interior_boundary

@preamble
A set with an empty boundary is one whose closure has nothing its interior lacks, so the three sets in the line coincide — and a set that equals its interior is open, while a set that equals its closure is closed.

The converse is the same sentence read backwards: if `S` is both open and closed, the closure and the interior are both `S`, and one taken from the other leaves nothing.

The sets that are both, in any space, are the ones that split it: the empty set and the whole space always, and more exactly when the space falls apart.
@description
Prove that `T.boundary S = ∅` exactly when `S` is open and closed. `Set.sdiff_eq_empty` turns an empty difference into a containment, after a `have` restates the boundary as the difference it is; the two equivalences proved above then convert between openness and the two equalities.
-/
theorem Topology.boundary_eq_empty_iff {X : Type u} (T : Topology X) (S : Set X) :
    T.boundary S = ∅ ↔ T.IsOpen S ∧ T.IsClosed S := by
  have hb : T.boundary S = T.closure S \ T.interior S := rfl
  rw [hb, Set.sdiff_eq_empty]
  constructor
  · intro h
    constructor
    · rw [T.isOpen_iff_interior_eq]
      exact Set.Subset.antisymm (T.interior_subset S) ((T.subset_closure S).trans h)
    · rw [T.isClosed_iff_closure_eq]
      exact Set.Subset.antisymm (h.trans (T.interior_subset S)) (T.subset_closure S)
  · rintro ⟨hO, hC⟩
    rw [(T.isClosed_iff_closure_eq S).mp hC, (T.isOpen_iff_interior_eq S).mp hO]

/-!
@concept dense_sets
@title Dense Subsets
@kind definition
@goal

A set is dense when its closure is the whole space: every point is approached by it, and no nonempty open set avoids it. Density is how a small set stands in for a large one — the rationals for the line — and it is the first property of a subset that the topology alone can see, the metric having nothing to say about it.
-/

/-!
@problem define_dense
@title The Definition of a Dense Set
@concept dense_sets

@preamble
A subset `S` is *dense* when closing it gives everything: `T.closure S = Set.univ`. By the characterisation of the points of a closure, that says every point of the space is approached by `S` — no point of `X` has a neighbourhood free of it.

A dense set may be very much smaller than the space it is dense in, which is what makes the notion useful. The space itself is dense in itself, and so is anything the closure drags out to everything.
@description
Define `Topology.Dense`, which says of a topology `T` and a set `S` that the closure of `S` is `Set.univ`. It returns a `Prop`, since it is a property of `S` and not a set.
-/

def Topology.Dense {X : Type u} (T : Topology X) (S : Set X) : Prop :=
  T.closure S = Set.univ

/-- @spec -/
example (X : Type) (T : Topology X) (S : Set X) : T.Dense S ↔ T.closure S = Set.univ := Iff.rfl

/-! @end -/

/--
@problem dense_iff_meets_open
@title Dense Means Meeting Every Nonempty Open Set
@concept dense_sets

@preamble
Density is a statement about the closure, and the closure is known point by point, so density is known open set by open set: `S` is dense exactly when every nonempty open set contains a point of `S`.

Forwards: a nonempty open `U` holds some `x`, which lies in the closure since the closure is everything, and `U` is a neighbourhood of `x`, so `U` meets `S`.

Backwards: to put an arbitrary `x` in the closure, take any neighbourhood `N` of `x` and the open `U` with `x ∈ U ⊆ N`; that `U` is nonempty, so it meets `S`, and so does `N`.
@description
Prove that `T.Dense S` exactly when `(U ∩ S).Nonempty` for every open `U` that is `U.Nonempty`. `show` restates a `Dense` goal as the equation it abbreviates, `Set.eq_univ_of_forall` proves a set is everything one point at a time, and `T.mem_closure_iff` is the characterisation to use in both directions.
-/
theorem Topology.dense_iff {X : Type u} (T : Topology X) (S : Set X) :
    T.Dense S ↔ ∀ U, T.IsOpen U → U.Nonempty → (U ∩ S).Nonempty := by
  constructor
  · rintro hd U hU ⟨x, hxU⟩
    have hx : x ∈ T.closure S := by
      rw [show T.closure S = Set.univ from hd]
      trivial
    exact T.mem_closure_iff.mp hx U (T.nbhd_of_isOpen hU hxU)
  · intro h
    show T.closure S = Set.univ
    apply Set.eq_univ_of_forall
    intro x
    apply T.mem_closure_iff.mpr
    rintro N ⟨U, hU, hxU, hUN⟩
    obtain ⟨y, hyU, hyS⟩ := h U hU ⟨x, hxU⟩
    exact ⟨y, hUN hyU, hyS⟩

/-!
@problem rationals_dense
@title The Rationals are Dense in the Line
@concept dense_sets

@preamble
Between any two distinct real numbers there is a rational one. That single fact — `exists_rat_btwn`, the Archimedean property of the line in the form we need it — says that the rationals are dense in the real line.

Let `x` be real and `ε > 0`. Applying it to `x - ε < x + ε` gives a rational `q` strictly between, and `|x - q| < ε` follows, so `q` lies in the ball of radius `ε` about `x`. Every ball about every point holds a rational, which by the metric characterisation of the closure is density.

The set of rationals inside the reals is `rationals`, the real numbers of the form `(q : ℝ)`.
@description
Show that `rationals` is dense in `line.toTopology`. Restate the goal with `show`, prove it a point at a time with `Set.eq_univ_of_forall`, and apply `line.mem_closure_iff` to reduce it to the balls. `abs_sub_lt_iff` splits an absolute value into the two inequalities `linarith` wants.
-/

/-- @given -/
def rationals : Set ℝ := {x | ∃ q : ℚ, (q : ℝ) = x}

theorem rationals_dense : line.toTopology.Dense rationals := by
  show line.toTopology.closure rationals = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  apply line.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x - ε < x + ε by linarith)
  refine ⟨(q : ℝ), ?_, ⟨q, rfl⟩⟩
  rw [line.mem_ball]
  show |x - (q : ℝ)| < ε
  rw [abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

/-! @end -/

end GeneralTopology
