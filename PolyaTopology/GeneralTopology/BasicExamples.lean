import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import PolyaTopology.GeneralTopology.TopologicalSpaces

/-! @section Basic Examples -/

universe u

namespace GeneralTopology

/-!
@concept extreme_topologies
@title The Two Extreme Topologies
@kind definition

Every set carries at least two topologies, and they are the ends of the range: one calls every subset open, the other only the two it must. Neither is interesting on its own; both are useful as bounds, as sources of counterexamples, and as a check that the axioms are weak enough to admit the trivial cases and strong enough to exclude nothing else.
-/

/-!
@problem define_discrete
@title The Discrete Topology
@concept extreme_topologies

@preamble
Call every subset open. The three conditions ask nothing, since the answer is always yes, so this is a topology on any set whatever — the *discrete* topology, the finest there is.

A field of a structure may be filled by a proof that ignores its hypotheses. `trivial` proves `True`.
@description
Define `discrete X`, whose `IsOpen` is `fun _ => True`. Each of the three conditions is `trivial`, the last two after their hypotheses are taken and discarded.
-/

def discrete (X : Type u) : TopologicalSpace X where
  IsOpen := fun _ => True
  isOpen_univ := trivial
  isOpen_inter := fun _ _ => trivial
  isOpen_sUnion := fun _ => trivial

/-- @spec -/
example (X : Type) (U : Set X) : (discrete X).IsOpen U ↔ True := Iff.rfl

/-! @end -/

/-!
@problem codiscrete_closure
@title Two Sets Are Closed Under Both Operations
@concept extreme_topologies

@preamble
Before the topology, the two facts it needs. Call a set *trivial* when it is `∅` or the whole space.

Two trivial sets intersect to a trivial one: if either is empty the intersection is empty, and otherwise both are everything and so is the intersection.

A union of trivial sets is trivial: if some member is the whole space then the union is too, being between that member and the whole; and if none is, every member is empty and so is the union.
@description
Prove the two. Each is a case analysis: `rcases` a hypothesis of the form `U = ∅ ∨ U = Set.univ` and the substitution does most of the work. For the union, split on `Set.univ ∈ F` with `by_cases`; `Set.subset_sUnion_of_mem` and `Set.subset_univ` sandwich one case and `Set.sUnion_eq_empty` reduces the other.
-/

theorem trivial_inter {X : Type u} {U V : Set X} (hU : U = ∅ ∨ U = Set.univ)
    (hV : V = ∅ ∨ V = Set.univ) : U ∩ V = ∅ ∨ U ∩ V = Set.univ := by
  rcases hU with rfl | rfl
  · left; exact Set.empty_inter V
  · rcases hV with rfl | rfl
    · left; exact Set.inter_empty _
    · right; exact Set.inter_self _

theorem trivial_sUnion {X : Type u} {F : Set (Set X)}
    (h : ∀ U ∈ F, U = ∅ ∨ U = Set.univ) : ⋃₀ F = ∅ ∨ ⋃₀ F = Set.univ := by
  by_cases hu : (Set.univ : Set X) ∈ F
  · exact Or.inr (Set.Subset.antisymm (Set.subset_univ _) (Set.subset_sUnion_of_mem hu))
  · refine Or.inl (Set.sUnion_eq_empty.mpr ?_)
    intro U hUF
    rcases h U hUF with rfl | rfl
    · rfl
    · exact absurd hUF hu

/-! @end -/

/-!
@problem define_codiscrete
@title The Indiscrete Topology
@concept extreme_topologies

@preamble
Now the other extreme: call open only what must be, the whole set and the empty set. This is the *indiscrete* topology, the coarsest there is. Older texts and the categorical literature call it indiscrete; Mathlib calls it indiscrete, and so do we.

With the two facts in hand there is nothing left to check — which is the same shape as the metric topology, where three theorems came first and the construction was a matter of naming them.
@description
Define `indiscrete X`, whose `IsOpen U` is `U = ∅ ∨ U = Set.univ`. The whole space is open on the right of the disjunction, and the other two fields are the two theorems above.
-/

def indiscrete (X : Type u) : TopologicalSpace X where
  IsOpen := fun U => U = ∅ ∨ U = Set.univ
  isOpen_univ := Or.inr rfl
  isOpen_inter := trivial_inter
  isOpen_sUnion := trivial_sUnion

/-- @spec -/
example (X : Type) (U : Set X) : (indiscrete X).IsOpen U ↔ (U = ∅ ∨ U = Set.univ) := Iff.rfl

/-! @end -/

/--
@problem codiscrete_is_coarsest
@title Every Topology Lies Between the Two
@concept extreme_topologies

@preamble
The two extremes bound every other topology on the same set. Whatever `T` is, anything the indiscrete topology calls open is open in `T` — the empty set and the whole set are open in every topology — and anything `T` calls open is open in the discrete one, which calls everything open.

So the topologies on a set are ordered by how many sets they call open, with these two at the ends. A finer topology has more open sets, and so more of everything defined from them.
@description
Prove both containments. For the first, take the disjunction apart and use `T.empty` and `T.isOpen_univ`; the second holds whatever the hypothesis says.
-/
theorem indiscrete_le_le_discrete {X : Type u} (T : TopologicalSpace X) {U : Set X} :
    ((indiscrete X).IsOpen U → T.IsOpen U) ∧ (T.IsOpen U → (discrete X).IsOpen U) := by
  constructor
  · rintro (rfl | rfl)
    · exact T.empty
    · exact T.isOpen_univ
  · intro _
    trivial

/-!
@concept sierpinski_space
@title The Sierpiński Space
@kind definition

The smallest space that is neither discrete nor indiscrete has two points, one of which is open and the other not. It is the standard source of the phenomena that vanish when a space is nice: two distinct points that no open set separates, and a point whose only neighbourhood is everything.
-/

/-!
@problem define_sierpinski
@title The Sierpiński Space
@concept sierpinski_space

@preamble
Take the two-element set `Bool` and declare a subset open when, if it contains `false`, it also contains `true`. Three subsets pass: the empty set, `{true}`, and the whole set. The fourth, `{false}`, fails, and that single asymmetry is the whole of the example.

Written this way each condition is an implication, and the proofs are short. That is the advantage of describing the open sets by a property rather than by listing them.
@description
Define `sierpinski`, a topology on `Bool` whose `IsOpen U` is `false ∈ U → true ∈ U`. The whole set holds it trivially; an intersection holds it from both halves; and for a union, the member that supplies `false` supplies `true`.
-/

def sierpinski : TopologicalSpace Bool where
  IsOpen := fun U => false ∈ U → true ∈ U
  isOpen_univ := fun _ => trivial
  isOpen_inter := fun hU hV h => ⟨hU h.1, hV h.2⟩
  isOpen_sUnion := by
    intro F h hf
    obtain ⟨U, hUF, hU⟩ := hf
    exact ⟨U, hUF, h U hUF hU⟩

/-- @spec -/
example (U : Set Bool) : sierpinski.IsOpen U ↔ (false ∈ U → true ∈ U) := Iff.rfl

/-! @end -/

/--
@problem sierpinski_point_not_open
@title One of the Two Points is Not Open
@concept sierpinski_space

@preamble
The set `{false}` is not open, and that is what makes the space worth naming. Its single point contains `false` and not `true`, so the defining implication fails at once.

The consequence is that `false` has no small neighbourhood: every open set containing it also contains `true`, so the two points cannot be told apart by open sets from that side, though they can from the other.
@description
Show that `{false}` is not open in `sierpinski`. Assume it is, apply the implication to the membership `false ∈ {false}`, and the result says `true = false`, which `simp` refutes.
-/
theorem sierpinski_singleton_false_not_open : ¬ sierpinski.IsOpen {false} := by
  intro h
  have : (true : Bool) ∈ ({false} : Set Bool) := h rfl
  simp at this

/-!
@concept cofinite_topology
@title The Cofinite Topology
@kind definition

On any set, calling a subset open when it leaves out only finitely many points gives a topology. It is the first example whose conditions really have to be checked, and the first where the asymmetry between two and any number does visible work: complements of finitely many open sets stay finite because a finite union of finite sets is finite.
-/

/-!
@problem cofinite_closure
@title Cofinite Sets Are Closed Under Both Operations
@concept cofinite_topology

@preamble
Call a subset open when it is empty, or when its complement is finite. On a finite set this is just the discrete topology; on an infinite one it is a genuinely new example, and a small one, since any two nonempty open sets must meet.

The two conditions come out of two facts about finite sets. For an intersection, `(U ∩ V)ᶜ = Uᶜ ∪ Vᶜ`, and a union of two finite sets is finite. For a union, the complement of `⋃₀ F` is contained in the complement of any one member, and a subset of a finite set is finite.
@description
Prove the two closure facts for sets that are empty or have a finite complement. For the intersection, `rcases` both hypotheses, then `Set.compl_inter` and `Set.Finite.union`. For the union, split with `by_cases` on whether some member is nonempty: if one is, its complement is finite and `Set.compl_subset_compl` with `Set.Finite.subset` finishes; if none is, `by_contra` shows every member empty.
-/

theorem cofinite_inter {X : Type u} {U V : Set X} (hU : U = ∅ ∨ Uᶜ.Finite)
    (hV : V = ∅ ∨ Vᶜ.Finite) : U ∩ V = ∅ ∨ (U ∩ V)ᶜ.Finite := by
  rcases hU with rfl | hu
  · left; exact Set.empty_inter V
  · rcases hV with rfl | hv
    · left; exact Set.inter_empty U
    · right; rw [Set.compl_inter]; exact hu.union hv

theorem cofinite_sUnion {X : Type u} {F : Set (Set X)}
    (h : ∀ U ∈ F, U = ∅ ∨ Uᶜ.Finite) : ⋃₀ F = ∅ ∨ (⋃₀ F)ᶜ.Finite := by
  by_cases he : ∃ U ∈ F, U ≠ ∅
  · obtain ⟨U, hUF, hne⟩ := he
    refine Or.inr (((h U hUF).resolve_left hne).subset ?_)
    exact Set.compl_subset_compl.mpr (Set.subset_sUnion_of_mem hUF)
  · refine Or.inl (Set.sUnion_eq_empty.mpr ?_)
    intro U hUF
    by_contra hne
    exact he ⟨U, hUF, hne⟩

/-! @end -/

/-!
@problem define_cofinite
@title The Cofinite Topology
@concept cofinite_topology

@preamble
With the two facts proved, the topology assembles. Only the whole space is left, and its complement is empty, which is finite.
@description
Define `cofinite X`, whose `IsOpen U` is `U = ∅ ∨ Uᶜ.Finite`. For the whole space, `Set.compl_univ` and `Set.finite_empty`; the other two fields are the two theorems above.
-/

def cofinite (X : Type u) : TopologicalSpace X where
  IsOpen := fun U => U = ∅ ∨ Uᶜ.Finite
  isOpen_univ := Or.inr (by rw [Set.compl_univ]; exact Set.finite_empty)
  isOpen_inter := cofinite_inter
  isOpen_sUnion := cofinite_sUnion

/-- @spec -/
example (X : Type) (U : Set X) : (cofinite X).IsOpen U ↔ (U = ∅ ∨ Uᶜ.Finite) := Iff.rfl

/-! @end -/

/-!
@concept subspace_topology
@title The Subspace Topology
@kind definition

A subset of a topological space is a topological space in its own right, with the sets cut out of the ambient open sets by intersection. This is how every space met in practice arises — a curve, a surface, a solid is a subset of a Euclidean space — and it is the first construction that makes new spaces out of old, which is what the rest of the subject does.
-/

/-!
@problem define_subspace
@title A Subset is a Space
@concept subspace_topology

@preamble
Let `A` be a subset of a space `X`. A point of `A` is a term of the type `A` — a point of `X` together with a proof it lies in `A` — and `Subtype.val` sends it back. A subset of `A` is called open when it is what an open set of `X` leaves behind: `V = Subtype.val ⁻¹' U` for some open `U`.

The conditions transfer because taking preimages commutes with both operations. The union needs one turn of thought: the collection to unite in `X` is the open sets whose trace lies in the given collection, and that is enough, because every member of the collection is the trace of one of them.
@description
Define `TopologicalSpace.subspace`, the topology `T` induces on `A`. For the whole set take `Set.univ`; for an intersection, `rintro` the two witnesses with `rfl` and offer their intersection. For the union, offer `⋃₀ {U | T.IsOpen U ∧ Subtype.val ⁻¹' U ∈ F}` and prove the two containments with `Set.Subset.antisymm`.
-/

def TopologicalSpace.subspace {X : Type u} (T : TopologicalSpace X) (A : Set X)
    : TopologicalSpace A where
  IsOpen := fun V => ∃ U, T.IsOpen U ∧ V = Subtype.val ⁻¹' U
  isOpen_univ := ⟨Set.univ, T.isOpen_univ, rfl⟩
  isOpen_inter := by
    rintro V W ⟨U, hU, rfl⟩ ⟨U', hU', rfl⟩
    exact ⟨U ∩ U', T.isOpen_inter hU hU', rfl⟩
  isOpen_sUnion := by
    intro F h
    refine ⟨⋃₀ {U | T.IsOpen U ∧ (Subtype.val ⁻¹' U : Set A) ∈ F},
      T.isOpen_sUnion (fun U hU => hU.1), ?_⟩
    apply Set.Subset.antisymm
    · rintro x ⟨V, hVF, hxV⟩
      obtain ⟨U, hU, rfl⟩ := h V hVF
      exact ⟨U, ⟨hU, hVF⟩, hxV⟩
    · rintro x ⟨U, ⟨hU, hUF⟩, hxU⟩
      exact ⟨_, hUF, hxU⟩

/-- @spec -/
example (X : Type) (T : TopologicalSpace X) (A : Set X) (V : Set A) :
    (T.subspace A).IsOpen V ↔ ∃ U, T.IsOpen U ∧ V = Subtype.val ⁻¹' U := Iff.rfl

/-! @end -/

end GeneralTopology
