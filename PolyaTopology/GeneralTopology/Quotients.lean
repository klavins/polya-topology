import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Products

/-! @section Quotients and Sums -/

universe u v w

namespace GeneralTopology

/-!
@concept final_topology
@title The Final Topology
@kind definition

The induced topology pulls the open sets back along a map into a space. Reverse the arrow: given a map out of a space, call a set open below when its preimage is open above. This is the finest topology making that map continuous, and every space built by gluing — a quotient, a disjoint union — carries it.
-/

/--
@problem preimage_of_union
@title The Preimage of a Union
@concept final_topology

@preamble
Everything in this section rests on one fact about preimages: they commute with the three operations a topology is closed under. For the whole space and for an intersection Mathlib states this already. For a union of a family it is worth proving, because the family on the other side has to be built.

Given a collection `F` of subsets of `Y`, the collection of their preimages is `Set.preimage f '' F`, the image of `F` under the operation that takes a preimage. A point lies in the union of that collection exactly when it lies in the preimage of some member of `F`, which is exactly when its image lies in the union of `F`.
@description
Prove that `f ⁻¹' (⋃₀ F) = ⋃₀ (Set.preimage f '' F)`. `Set.Subset.antisymm` splits the equality, and each direction takes a membership apart with `rintro` and offers the corresponding member of the other collection.
-/
theorem preimage_sUnion_image {X : Type u} {Y : Type v} (f : X → Y) (F : Set (Set Y)) :
    f ⁻¹' (⋃₀ F) = ⋃₀ (Set.preimage f '' F) := by
  apply Set.Subset.antisymm
  · rintro x ⟨V, hVF, hxV⟩
    exact ⟨f ⁻¹' V, ⟨V, hVF, rfl⟩, hxV⟩
  · rintro x ⟨W, ⟨V, hVF, rfl⟩, hxW⟩
    exact ⟨V, hVF, hxW⟩

/-!
@problem define_coinduced
@title The Topology Coinduced by a Map
@concept final_topology

@preamble
Let `f` carry a space `X` to a set `Y`. Call a subset of `Y` open when its preimage under `f` is open in `X`. The three conditions then hold for the reason just proved: a preimage commutes with each of the three operations, so each condition is the corresponding condition upstairs.

Written this way the definition is shorter than the induced one, which had to say "is the preimage of an open set" and carry an existential to say it. Here there is no existential, because the test is applied to the set itself.
@description
Define `Topology.coinduced`, the topology on `Y` whose `IsOpen V` says `T.IsOpen (f ⁻¹' V)`. `Set.preimage_univ` and `Set.preimage_inter` rewrite the first two fields; the third rewrites by the previous problem and then applies the union condition of `T` to the collection of preimages.
-/

def Topology.coinduced {X : Type u} {Y : Type v} (T : Topology X) (f : X → Y) : Topology Y where
  IsOpen := fun V => T.IsOpen (f ⁻¹' V)
  univ := by
    rw [Set.preimage_univ]
    exact T.univ
  inter := by
    intro V W hV hW
    rw [Set.preimage_inter]
    exact T.inter hV hW
  sUnion := by
    intro F h
    rw [preimage_sUnion_image]
    refine T.sUnion ?_
    rintro W ⟨V, hVF, rfl⟩
    exact h V hVF

/-- @spec -/
example (X Y : Type) (T : Topology X) (f : X → Y) (V : Set Y) :
    (T.coinduced f).IsOpen V ↔ T.IsOpen (f ⁻¹' V) := Iff.rfl

/-! @end -/

/-!
@problem coinduced_continuous
@title The Finest Topology Making a Map Continuous
@concept final_topology

@preamble
The coinduced topology was built to make `f` continuous, and it does with nothing to check: the preimage of a set it calls open is open by definition.

It is the largest topology that does, which is the mirror of what the induced topology satisfied. If `S` is any topology on `Y` for which `f` is continuous, then every set `S` calls open has an open preimage, and an open preimage is all the coinduced topology asks. So the coinduced topology calls open everything `f` permits, where the induced one called open only what its map forced.
@description
Show that `f` is continuous from `T` to `T.coinduced f`, and that `T.coinduced f` calls open every set a topology `S` calls open, whenever `f` is continuous into `S`. Each is the hypothesis applied at the set, with nothing in between.
-/

theorem Topology.continuous_coinduced {X : Type u} {Y : Type v} (T : Topology X) (f : X → Y) :
    T.Continuous (T.coinduced f) f :=
  fun _ hV => hV

theorem Topology.coinduced_finest {X : Type u} {Y : Type v} {T : Topology X} {S : Topology Y}
    {f : X → Y} (hf : T.Continuous S f) {V : Set Y} (hV : S.IsOpen V) :
    (T.coinduced f).IsOpen V :=
  hf V hV

/-! @end -/

/--
@problem coinduced_universal
@title A Map Out of a Coinduced Topology
@concept final_topology

@preamble
A subspace was never examined directly: a map into it was tested by composing with the inclusion. The same holds here, in the other direction. A map `g` out of a space carrying the coinduced topology is continuous exactly when `g ∘ f` is, so no open set of `Y` ever has to be looked at.

One direction is composition with `f`. For the other, the preimage under `g` of an open set of `Z` is called open when its preimage under `f` is open, and that is the preimage under the composite.
@description
Prove that `(T.coinduced f).Continuous S g` exactly when `T.Continuous S (g ∘ f)`. Forwards, compose with the previous problem. Backwards, restate the goal with `show`, fold the two preimages into one with `← Set.preimage_comp`, and apply the hypothesis.
-/
theorem Topology.continuous_out_of_coinduced {X : Type u} {Y : Type v} {Z : Type w}
    (T : Topology X) (f : X → Y) (S : Topology Z) (g : Y → Z) :
    (T.coinduced f).Continuous S g ↔ T.Continuous S (g ∘ f) := by
  constructor
  · intro hg
    exact Topology.continuous_comp T (Topology.continuous_coinduced T f) hg
  · intro hg W hW
    show T.IsOpen (f ⁻¹' (g ⁻¹' W))
    rw [← Set.preimage_comp]
    exact hg W hW

/-!
@concept lean_quotients
@title Quotients in Lean
@kind definition

An equivalence relation on a set gives the set of its classes. In Lean the relation is bundled with its proof of being one as a `Setoid`, and `Quotient` builds the type of classes out of it. Three things are needed of that type: that every element of it is a class, when two classes are equal, and how a map out of it is given. None of them is topology.
-/

/-!
@problem define_kernel_setoid
@title The Relation a Map Induces
@concept lean_quotients

@preamble
A `Setoid X` bundles a relation `r : X → X → Prop` with a proof `iseqv` that it is an equivalence — reflexive, symmetric, transitive — exactly as `Metric` bundled a distance with its axioms. We write `s.r x y` for the relation of a setoid `s`.

Every map produces one. Call `x` and `y` equivalent when `f x = f y`. This is an equivalence relation because equality is one, and the three fields of `Equivalence` are the three corresponding facts about equality. Any map out of `X` identifies exactly the pairs this relation names, so this is the general shape of a relation worth quotienting by.
@description
Define `kernelSetoid f`, whose relation is `fun x y => f x = f y`. The `iseqv` field is an anonymous constructor of three proofs: `rfl` for the first, and `Eq.symm` and `Eq.trans` applied to the hypotheses for the other two.
-/

def kernelSetoid {X : Type u} {Y : Type v} (f : X → Y) : Setoid X where
  r := fun x y => f x = f y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- @spec -/
example (X Y : Type) (f : X → Y) (x y : X) : (kernelSetoid f).r x y ↔ f x = f y := Iff.rfl

/-! @end -/

/-!
@problem quotient_mk_facts
@title Every Element of a Quotient is a Class
@concept lean_quotients

@preamble
`Quotient s` is the type of classes of `s`, and `Quotient.mk s x` is the class of `x`. Two facts fix it completely.

Every element of `Quotient s` is the class of some point. The tool is `Quotient.inductionOn`: to prove something of every `q`, it is enough to prove it of every `Quotient.mk s x`.

Two points have the same class exactly when they are related. The two directions are `Quotient.exact` and `Quotient.sound`, and between them they say what a quotient is: it forgets the relation, and forgets nothing else.
@description
Prove that every `q : Quotient s` is `Quotient.mk s x` for some `x`, and that `Quotient.mk s x = Quotient.mk s y` exactly when `s.r x y`. For the first, apply `Quotient.inductionOn` to `q` and offer the point with `rfl`; the second is the two named theorems as the halves of an anonymous constructor.
-/

theorem quotient_mk_surjective {X : Type u} (s : Setoid X) (q : Quotient s) :
    ∃ x, Quotient.mk s x = q :=
  Quotient.inductionOn q (fun x => ⟨x, rfl⟩)

theorem quotient_mk_eq_iff {X : Type u} (s : Setoid X) (x y : X) :
    Quotient.mk s x = Quotient.mk s y ↔ s.r x y :=
  ⟨Quotient.exact, Quotient.sound⟩

/-! @end -/

/-!
@problem kernel_lift
@title A Map Out of a Quotient
@concept lean_quotients

@preamble
To give a map out of `Quotient s` is to give a map out of `X` that does not distinguish related points. `Quotient.lift f h` is that map, where `h` proves `f a = f b` whenever `a` and `b` are related, and `Quotient.lift f h (Quotient.mk s x) = f x` holds by definition.

For the relation a map induces, the obligation is that relation itself, so the proof asked for is the hypothesis unchanged. The map that results is injective: two classes with the same value are the classes of two points with the same image under `f`, and that is what being related means here.
@description
Define `kernelLift f`, the map `Quotient (kernelSetoid f) → Y` that `f` descends to, and show that it is injective. For the second, take both classes apart with `induction … using Quotient.inductionOn` and close with `Quotient.sound` applied to the hypothesis.
-/

def kernelLift {X : Type u} {Y : Type v} (f : X → Y) : Quotient (kernelSetoid f) → Y :=
  Quotient.lift f (fun _ _ h => h)

theorem kernelLift_injective {X : Type u} {Y : Type v} (f : X → Y)
    {p q : Quotient (kernelSetoid f)} (h : kernelLift f p = kernelLift f q) : p = q := by
  induction p using Quotient.inductionOn with
  | _ x =>
    induction q using Quotient.inductionOn with
    | _ y => exact Quotient.sound h

/-- @spec -/
example (X Y : Type) (f : X → Y) (x : X) :
    kernelLift f (Quotient.mk (kernelSetoid f) x) = f x := rfl

/-! @end -/

/-!
@concept quotient_space
@title The Quotient Space
@kind definition

Gluing points together is the first construction that makes a space smaller rather than larger. The set of classes carries the final topology along the map sending a point to its class, so a set of classes is open exactly when the points those classes collect form an open set. Every space made by identification is one of these.
-/

/-!
@problem define_quotient_topology
@title The Quotient Topology
@concept quotient_space

@preamble
Let `s` be a setoid on a space `X`. The quotient carries the final topology along `Quotient.mk s`: a set of classes is open exactly when the set of points belonging to those classes is open in `X`.

Nothing new has to be built, since the construction is already in hand and this is one instance of it. What the definition buys is a name, and with the name the continuity of the projection — which is the continuity of a map into the topology that map coinduces, and so was proved before the quotient was mentioned.
@description
Define `Topology.quotient` as `T.coinduced (Quotient.mk s)`, and show that `Quotient.mk s` is continuous into it. The second is the corresponding theorem about the coinduced topology, at the map `Quotient.mk s`.
-/

def Topology.quotient {X : Type u} (T : Topology X) (s : Setoid X) : Topology (Quotient s) :=
  T.coinduced (Quotient.mk s)

theorem Topology.continuous_mk {X : Type u} (T : Topology X) (s : Setoid X) :
    T.Continuous (T.quotient s) (Quotient.mk s) :=
  Topology.continuous_coinduced T (Quotient.mk s)

/-- @spec -/
example (X : Type) (T : Topology X) (s : Setoid X) (V : Set (Quotient s)) :
    (T.quotient s).IsOpen V ↔ T.IsOpen (Quotient.mk s ⁻¹' V) := Iff.rfl

/-! @end -/

/--
@problem quotient_universal
@title The Descended Map is Continuous
@concept quotient_space

@preamble
A continuous map that does not distinguish related points descends to the quotient, and the descended map is continuous. This is the property the quotient topology was chosen to have, and it is what lets a quotient be used without its definition ever being unfolded again.

There is nothing left to prove. The descended map composed with the projection is the original map, so the general statement about maps out of a coinduced topology applies as it stands.
@description
Show that `Quotient.lift f h` is continuous from `T.quotient s` whenever `f` is. Apply the `.mpr` of the coinduced universal property, at the map `Quotient.mk s` and the map `Quotient.lift f h`; the composite is `f` by definition, so the hypothesis closes it.
-/
theorem Topology.continuous_quotient_lift {X : Type u} {Z : Type w} {T : Topology X}
    {s : Setoid X} {S : Topology Z} {f : X → Z} (h : ∀ a b, s.r a b → f a = f b)
    (hf : T.Continuous S f) : (T.quotient s).Continuous S (Quotient.lift f h) := by
  apply (Topology.continuous_out_of_coinduced T (Quotient.mk s) S (Quotient.lift f h)).mpr
  exact hf

/-!
@problem saturated_sets
@title Saturated Sets
@concept quotient_space

@preamble
A projection collapses points, so it carries most sets to sets one can say little about. The exceptions are the sets that are already unions of whole classes: of those, nothing is lost and nothing is added.

Say that `S` is *saturated* for `f` when `S` is the preimage of its image, `S = f ⁻¹' (f '' S)`. One containment always holds, since a point lies in the preimage of the image of any set it belongs to, so the condition is the other one: no point outside `S` shares an image with a point of `S`.

Preimages are where they come from. The preimage of any set is saturated, because taking an image and then a preimage adds nothing to a set that was a preimage already.
@description
Define `IsSaturated f S` as the equation above, in that order, and prove that `f ⁻¹' V` is saturated for every `V`. `Set.Subset.antisymm` splits the equality; the first containment offers the point itself, and the second rewrites backwards along the equation of images the membership carries.
-/

def IsSaturated {X : Type u} {Y : Type v} (f : X → Y) (S : Set X) : Prop :=
  S = f ⁻¹' (f '' S)

theorem isSaturated_preimage {X : Type u} {Y : Type v} (f : X → Y) (V : Set Y) :
    IsSaturated f (f ⁻¹' V) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · rintro x ⟨y, hy, hxy⟩
    show f x ∈ V
    rw [← hxy]
    exact hy

/-! @end -/

/--
@problem quotient_open_saturated
@title Open Saturated Sets Have Open Images
@concept quotient_space

@preamble
A projection need not be an open map. The image of an open set is open exactly when the test the final topology applies comes out yes, and that test asks about the preimage of the image — which is the saturation of the set, and not the set.

On a saturated set the question therefore answers itself. There the preimage of the image is the set, which was assumed open.
@description
Show that `f '' S` is open in `T.coinduced f` when `S` is open and saturated for `f`. Restate the goal with `show`, rewrite backwards along the saturation, and the hypothesis is what remains.
-/
theorem Topology.isOpen_image_of_saturated {X : Type u} {Y : Type v} (T : Topology X) (f : X → Y)
    {S : Set X} (hS : T.IsOpen S) (hsat : IsSaturated f S) : (T.coinduced f).IsOpen (f '' S) := by
  show T.IsOpen (f ⁻¹' (f '' S))
  rw [← hsat]
  exact hS

/-!
@problem quotient_discrete
@title A Quotient of a Discrete Space
@concept quotient_space

@preamble
The finest topology of all survives every identification. If every subset of `X` is open then every subset of `Y` has an open preimage, whatever the map is, so the coinduced topology calls every subset open and is the discrete topology on `Y`.

Two topologies are equal as soon as they call the same sets open, and here the two conditions are not merely equivalent but the same proposition. The quotient is the case of the map that takes a point to its class.
@description
Prove that `(discrete X).coinduced f = discrete Y` for every `f`, and deduce the same of the quotient by any setoid. `Topology.eq_of_isOpen_iff` reduces the first to an equivalence at each set, and both sides of that are `True`.
-/

theorem coinduced_discrete {X : Type u} {Y : Type v} (f : X → Y) :
    (discrete X).coinduced f = discrete Y :=
  Topology.eq_of_isOpen_iff (fun _ => Iff.rfl)

theorem quotient_discrete {X : Type u} (s : Setoid X) :
    (discrete X).quotient s = discrete (Quotient s) :=
  coinduced_discrete (Quotient.mk s)

/-! @end -/

/-!
@concept sum_space
@title The Sum of Two Spaces
@kind definition

Two spaces laid side by side, touching nowhere. A point is a point of one or a point of the other, and a set is open when the part of it lying in each is open there. This is the construction dual to the product: where a map into a product is a pair of maps, a map out of a sum is a pair of maps.
-/

/-!
@problem define_sum_topology
@title The Disjoint Union of Two Spaces
@concept sum_space

@preamble
The type `X ⊕ Y` holds a copy of `X` and a copy of `Y` with nothing in common: a term of it is `Sum.inl x` or `Sum.inr y`, and never both. A subset `W` of it meets each copy in a set, namely `Sum.inl ⁻¹' W` and `Sum.inr ⁻¹' W`.

Call `W` open when both of those are open. As with the coinduced topology, the three conditions hold because a preimage commutes with the three operations — twice over here, once on each side.
@description
Define `Topology.sum`, whose `IsOpen W` is the conjunction of `T.IsOpen (Sum.inl ⁻¹' W)` and `T'.IsOpen (Sum.inr ⁻¹' W)`, in that order. Each field rewrites both preimages — the third by the first problem of the section — and then offers the pair of conditions from `T` and `T'`.
-/

def Topology.sum {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    Topology (X ⊕ Y) where
  IsOpen := fun W => T.IsOpen (Sum.inl ⁻¹' W) ∧ T'.IsOpen (Sum.inr ⁻¹' W)
  univ := by
    rw [Set.preimage_univ, Set.preimage_univ]
    exact ⟨T.univ, T'.univ⟩
  inter := by
    intro V W hV hW
    rw [Set.preimage_inter, Set.preimage_inter]
    exact ⟨T.inter hV.1 hW.1, T'.inter hV.2 hW.2⟩
  sUnion := by
    intro F h
    rw [preimage_sUnion_image, preimage_sUnion_image]
    constructor
    · exact T.sUnion (by rintro W ⟨V, hVF, rfl⟩; exact (h V hVF).1)
    · exact T'.sUnion (by rintro W ⟨V, hVF, rfl⟩; exact (h V hVF).2)

/-- @spec -/
example (X Y : Type) (T : Topology X) (T' : Topology Y) (W : Set (X ⊕ Y)) :
    (T.sum T').IsOpen W ↔ T.IsOpen (Sum.inl ⁻¹' W) ∧ T'.IsOpen (Sum.inr ⁻¹' W) := Iff.rfl

/-! @end -/

/-!
@problem sum_injections_continuous
@title The Two Injections Are Continuous
@concept sum_space

@preamble
`Sum.inl` puts `X` into the sum and `Sum.inr` puts `Y` in. Each is continuous, and the definition was written so that there is nothing left to say: the preimage of an open `W` under `Sum.inl` is the first of the two things being open asks of `W`, and the preimage under `Sum.inr` is the second.
@description
Show that `Sum.inl` and `Sum.inr` are continuous into `T.sum T'`. Each is one half of the hypothesis, taken with `.1` or `.2`.
-/

theorem Topology.continuous_inl {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    T.Continuous (T.sum T') Sum.inl :=
  fun _ hW => hW.1

theorem Topology.continuous_inr {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    T'.Continuous (T.sum T') Sum.inr :=
  fun _ hW => hW.2

/-! @end -/

/-!
@problem sum_injections_open
@title The Two Injections Are Open Maps
@concept sum_space

@preamble
More is true: each injection carries open sets to open sets, which the inclusion of a subspace generally does not.

Take an open `U` of `X`. Its image under `Sum.inl` meets the first copy in `U` itself, since `Sum.inl` is injective, and meets the second copy in nothing at all, since no term of the sum is both an `inl` and an `inr`. The first of those is open by hypothesis, and the second is the empty set.
@description
Show that `Sum.inl` and `Sum.inr` are open maps into `T.sum T'`. `Set.preimage_image_eq`, with `Sum.inl_injective` or `Sum.inr_injective`, gives the preimage on the near side; `Set.preimage_inr_image_inl` and `Set.preimage_inl_image_inr` give the empty one on the far side.
-/

theorem Topology.isOpenMap_inl {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    T.IsOpenMap (T.sum T') Sum.inl := by
  intro U hU
  constructor
  · rw [Set.preimage_image_eq U Sum.inl_injective]
    exact hU
  · rw [Set.preimage_inr_image_inl]
    exact Topology.empty T'

theorem Topology.isOpenMap_inr {X : Type u} {Y : Type v} (T : Topology X) (T' : Topology Y) :
    T'.IsOpenMap (T.sum T') Sum.inr := by
  intro U hU
  constructor
  · rw [Set.preimage_inl_image_inr]
    exact Topology.empty T
  · rw [Set.preimage_image_eq U Sum.inr_injective]
    exact hU

/-! @end -/

/-!
@problem sum_universal
@title A Map Out of a Sum is a Pair of Maps
@concept sum_space

@preamble
To give a map from `X ⊕ Y` into `Z` is to give a map from `X` and a map from `Y`, since a point of the sum is one or the other. `Sum.elim f g` is that map: it applies `f` on the first copy and `g` on the second.

The topology was chosen so that the same holds of continuity, and again the proof is nothing. The preimage of a set under `Sum.elim f g`, read on the first copy, is its preimage under `f`, and read on the second copy, its preimage under `g`.
@description
Prove that `Sum.elim f g` is continuous when `f` and `g` are, and then that a map `h : X ⊕ Y → Z` is continuous exactly when `h ∘ Sum.inl` and `h ∘ Sum.inr` are. Both are pairs of applications of the hypotheses, and neither needs any rewriting.
-/

theorem Topology.continuous_sum_elim {X : Type u} {Y : Type v} {Z : Type w} {T : Topology X}
    {T' : Topology Y} (S : Topology Z) {f : X → Z} {g : Y → Z} (hf : T.Continuous S f)
    (hg : T'.Continuous S g) : (T.sum T').Continuous S (Sum.elim f g) :=
  fun W hW => ⟨hf W hW, hg W hW⟩

theorem Topology.continuous_sum_iff {X : Type u} {Y : Type v} {Z : Type w} (T : Topology X)
    (T' : Topology Y) (S : Topology Z) (h : X ⊕ Y → Z) :
    (T.sum T').Continuous S h ↔
      T.Continuous S (h ∘ Sum.inl) ∧ T'.Continuous S (h ∘ Sum.inr) := by
  constructor
  · intro hh
    exact ⟨fun W hW => (hh W hW).1, fun W hW => (hh W hW).2⟩
  · rintro ⟨hf, hg⟩ W hW
    exact ⟨hf W hW, hg W hW⟩

/-! @end -/

/-!
@concept quotient_examples
@title Collapsing a Subset
@kind theorem
@goal

The first identification worth making: take a subset, declare all of its points equal, and leave everything else alone. The space that results has one new point where the subset was. What that point inherits from the subset is the question the construction is for, and the answer for a closed subset is the last thing this subject proves.
-/

/-!
@problem define_collapse
@title The Relation That Collapses a Subset
@concept quotient_examples

@preamble
Fix a subset `A` of a set `X`. Declare `x` and `y` equivalent when they are equal, or when both of them lie in `A`. Outside `A` this is equality; inside `A` everything is equivalent to everything.

It is an equivalence relation. Reflexivity is the first disjunct. Symmetry swaps whichever disjunct holds. Transitivity has four cases, and in each the answer can be read off: two equalities compose, an equality on either side carries the pair of memberships across, and two pairs of memberships give the outer one.
@description
Define `collapse A`, whose relation is `fun x y => x = y ∨ (x ∈ A ∧ y ∈ A)`, in that order. Give the three fields of `Equivalence` as an anonymous constructor; a pattern such as `rintro x y (rfl | ⟨hx, hy⟩)` splits a hypothesis, and substituting the equality leaves the other disjunct to offer.
-/

def collapse {X : Type u} (A : Set X) : Setoid X where
  r := fun x y => x = y ∨ (x ∈ A ∧ y ∈ A)
  iseqv := ⟨fun _ => Or.inl rfl, by
      rintro x y (rfl | ⟨hx, hy⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx⟩, by
      rintro x y z (rfl | ⟨hx, hy⟩) (rfl | ⟨hy', hz⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hy', hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩⟩

/-- @spec -/
example (X : Type) (A : Set X) (x y : X) :
    (collapse A).r x y ↔ (x = y ∨ (x ∈ A ∧ y ∈ A)) := Iff.rfl

/-! @end -/

/--
@problem collapse_class
@title The Subset Becomes One Point
@concept quotient_examples

@preamble
The whole of `A` is one point of the quotient, and nothing outside `A` is that point. Said as a preimage: for any `a` of `A`, the set of points whose class is the class of `a` is `A` itself.

Forwards, a point with the class of `a` is related to `a`, so it is either equal to `a`, which lies in `A`, or it lies in `A` by the second disjunct. Backwards, any two points of `A` are related, so their classes agree.
@description
Prove that `Quotient.mk (collapse A) ⁻¹' {Quotient.mk (collapse A) a} = A` when `a ∈ A`. `Set.Subset.antisymm` splits it. A membership in a singleton is an equation of classes, which `Quotient.exact` turns into the relation and `Quotient.sound` turns back.
-/
theorem collapse_preimage_class {X : Type u} {A : Set X} {a : X} (ha : a ∈ A) :
    Quotient.mk (collapse A) ⁻¹' {Quotient.mk (collapse A) a} = A := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Quotient.exact hx with rfl | ⟨hxA, _⟩
    · exact ha
    · exact hxA
  · intro x hx
    exact Quotient.sound (Or.inr ⟨hx, ha⟩)

/-!
@problem interval_closed
@title The Unit Interval is Closed
@concept quotient_examples

@preamble
Before an interval is collapsed we check that it is closed, which is a statement about the line and needs no quotient at all. The set `unitInterval` is the reals `x` with `0 ≤ x ∧ x ≤ 1`.

A point outside it is either below `0` or above `1`. In the first case the distance to `0` is room to spare: every point within `-x` of `x` is still below `0`. In the second, every point within `x - 1` of `x` is still above `1`. So the complement has a ball around each of its points, which is what it is for the complement to be open.
@description
Show that `unitInterval` is closed in `line.toTopology`. Restate the goal with `show` as openness of the complement, split the failed conjunction with `not_and_or`, and offer the radius named above in each case. `abs_sub_lt_iff` turns a membership in a ball into the two inequalities `linarith` wants.
-/

/-- @given -/
def unitInterval : Set ℝ := {x | 0 ≤ x ∧ x ≤ 1}

theorem unitInterval_closed : line.toTopology.IsClosed unitInterval := by
  show line.IsOpenSet unitIntervalᶜ
  intro x hx
  rcases not_and_or.mp hx with h | h
  · refine ⟨-x, by linarith [not_le.mp h], ?_⟩
    intro y hy
    rw [Metric.mem_ball line, show line.dist x y = |x - y| from rfl, abs_sub_lt_iff] at hy
    exact fun hy' => absurd hy'.1 (by linarith [hy.1])
  · refine ⟨x - 1, by linarith [not_le.mp h], ?_⟩
    intro y hy
    rw [Metric.mem_ball line, show line.dist x y = |x - y| from rfl, abs_sub_lt_iff] at hy
    exact fun hy' => absurd hy'.2 (by linarith [hy.1])

/-! @end -/

/-!
@problem collapse_point_closed
@title Collapsing a Closed Set Leaves a Closed Point
@concept quotient_examples

@preamble
Now the two halves meet. The new point is closed in the quotient whenever the set collapsed was closed, because the preimage of the new point is that set — which the last problem but one proved — and the quotient calls a set closed exactly when its preimage is closed.

Applied to the line and the unit interval: the point that the interval became is a closed point of the quotient. The whole of the construction is a relation and the topology that relation coinduces.
@description
Prove that the class of a point of a closed `A` is a closed set of `T.quotient (collapse A)`, and read off the case of the line and the unit interval. For the first, restate the goal with `show`, move the complement across the preimage with `Set.preimage_compl`, and rewrite with `collapse_preimage_class`.
-/

theorem collapse_point_isClosed {X : Type u} (T : Topology X) {A : Set X} (hA : T.IsClosed A)
    {a : X} (ha : a ∈ A) :
    (T.quotient (collapse A)).IsClosed {Quotient.mk (collapse A) a} := by
  show T.IsOpen (Quotient.mk (collapse A) ⁻¹' {Quotient.mk (collapse A) a}ᶜ)
  rw [Set.preimage_compl, collapse_preimage_class ha]
  exact hA

theorem line_collapse_interval :
    (line.toTopology.quotient (collapse unitInterval)).IsClosed
      {Quotient.mk (collapse unitInterval) 0} :=
  collapse_point_isClosed line.toTopology unitInterval_closed ⟨le_refl 0, by norm_num⟩

/-! @end -/

end GeneralTopology
