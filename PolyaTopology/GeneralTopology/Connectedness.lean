import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Separation

/-! @section Connectedness -/

universe u v

namespace GeneralTopology

/-!
@concept connected
@title Connected Spaces
@kind definition

A space may fall into pieces that no open set straddles, and a topology says so without any help from a distance: a set both open and closed is a piece cut cleanly out. A space with no such piece but the two it cannot avoid is connected. It is the first property we ask of a space as a whole rather than of its points, and a subset may be asked for it too.
-/

/-!
@problem define_connected
@title Connected Spaces and Connected Sets
@concept connected

@preamble
A set that is both open and closed cuts the space in two: it and its complement are both open, they share no point, and together they are everything. Neither half can be reached from the other, and the topology sees no connection across the cut.

Every space has two such sets, the empty one and the whole space. A space is *connected* when it has no others.

A subset may be cut in the same way, and we ask the question with the open sets of the space around it rather than with those of the subspace. Two open sets that cover `S` and share no point of `S` divide it between them; `S` is connected when no such pair divides it, which is to say that `S` lies wholly inside one of the two.
@description
Define `Topology.IsConnected`, which says of a set that is open and closed — the two taken as separate hypotheses — that it is `∅` or `Set.univ`, the two disjuncts in that order. Then define `Topology.IsConnectedSet T S`: for all `U` and `V` with `T.IsOpen U`, `T.IsOpen V`, no point of `S` in both (written `∀ x ∈ S, x ∈ U → x ∉ V`) and `S ⊆ U ∪ V`, either `S ⊆ U` or `S ⊆ V`.
-/

def Topology.IsConnected {X : Type u} (T : Topology X) : Prop :=
  ∀ S, T.IsOpen S → T.IsClosed S → S = ∅ ∨ S = Set.univ

def Topology.IsConnectedSet {X : Type u} (T : Topology X) (S : Set X) : Prop :=
  ∀ U V, T.IsOpen U → T.IsOpen V → (∀ x ∈ S, x ∈ U → x ∉ V) → S ⊆ U ∪ V → S ⊆ U ∨ S ⊆ V

/-- @spec -/
example (X : Type) (T : Topology X) (S : Set X) :
    (T.IsConnected ↔ ∀ C, T.IsOpen C → T.IsClosed C → C = ∅ ∨ C = Set.univ)
      ∧ (T.IsConnectedSet S ↔ ∀ U V, T.IsOpen U → T.IsOpen V → (∀ x ∈ S, x ∈ U → x ∉ V) →
          S ⊆ U ∪ V → S ⊆ U ∨ S ⊆ V) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! @end -/

/-!
@problem subspace_trace
@title The Trace of a Set on a Subspace
@concept connected

@preamble
A subset `A` of `X` is a space in its own right, and its open sets are the traces `Subtype.val ⁻¹' U` of the open sets of `X`. A point of the subspace is a point `x` of `X` carrying a proof that `x ∈ A`, written `⟨x, hx⟩`, and it lies in a trace exactly when `x` lies in the set traced. Two facts about traces are all we need.

The trace of `U` is the whole of the subspace exactly when `A` lies inside `U`.

And if the trace of `V` is the complement of the trace of `U`, then no point of `A` lies in both `U` and `V`, and `A` lies inside their union. One equation, read in its two directions, gives both.
@description
Prove `trace_eq_univ_iff` and `trace_split`. Each direction turns a point `x` of `A` into the point `(⟨x, hx⟩ : A)` of the subspace and rewrites its membership along the equation given; `Set.eq_univ_of_forall` proves a set is everything one point at a time.
-/

theorem trace_eq_univ_iff {X : Type u} {A U : Set X} :
    (Subtype.val ⁻¹' U : Set A) = Set.univ ↔ A ⊆ U := by
  constructor
  · intro h x hx
    have hp : (⟨x, hx⟩ : A) ∈ (Subtype.val ⁻¹' U : Set A) := by rw [h]; trivial
    exact hp
  · intro h
    apply Set.eq_univ_of_forall
    intro p
    exact h p.2

theorem trace_split {X : Type u} {A U V : Set X}
    (h : (Subtype.val ⁻¹' U : Set A)ᶜ = Subtype.val ⁻¹' V) :
    (∀ x ∈ A, x ∈ U → x ∉ V) ∧ A ⊆ U ∪ V := by
  constructor
  · intro x hxA hxU hxV
    have hp : (⟨x, hxA⟩ : A) ∈ (Subtype.val ⁻¹' V : Set A) := hxV
    rw [← h] at hp
    exact hp hxU
  · intro x hxA
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · have hp : (⟨x, hxA⟩ : A) ∈ (Subtype.val ⁻¹' U : Set A)ᶜ := hxU
      rw [h] at hp
      exact Or.inr hp

/-! @end -/

/--
@problem connected_subspace
@title A Connected Set is a Connected Space
@concept connected

@preamble
The two definitions now meet. A set is connected in the ambient sense exactly when the space it carries — the subspace topology — is connected, and it is the direction from the set to the space that we prove.

Let `W` be a set of the subspace that is both open and closed. Being open, `W` is the trace of an open `U`; being closed, its complement is the trace of an open `V`. The facts about traces turn that pair into two open sets covering `A` and sharing none of its points, so `A` lies inside one of them: inside `U`, and `W` is the whole subspace; inside `V`, and the complement of `W` is, so `W` is empty.
@description
Show that `T.IsConnectedSet A` makes the subspace `A` a connected space. `rintro W ⟨U, hU, rfl⟩ ⟨V, hV, hVeq⟩` opens both hypotheses at once, naming the equation the closedness supplies, and `Set.compl_univ_iff` turns `Wᶜ = Set.univ` into `W = ∅`.
-/
theorem Topology.isConnected_subspace {X : Type u} (T : Topology X) {A : Set X}
    (h : T.IsConnectedSet A) : (T.subspace A).IsConnected := by
  rintro W ⟨U, hU, rfl⟩ ⟨V, hV, hVeq⟩
  obtain ⟨hno, hcov⟩ := trace_split hVeq
  rcases h U V hU hV hno hcov with h0 | h0
  · exact Or.inr (trace_eq_univ_iff.mpr h0)
  · left
    have hu := trace_eq_univ_iff.mpr h0
    rw [← hVeq] at hu
    exact Set.compl_univ_iff.mp hu

/-!
@concept connected_examples
@title Spaces That Are Connected, and Spaces That Are Not
@kind theorem

A definition earns its place by what it admits and what it rules out. At one extreme is a topology too coarse to cut anything out of a space; at the other, a two-point space that falls apart. Between them lies the theorem the subject has owed since the real line was defined: an interval does not fall apart, and the least upper bound property is what says so.
-/

/-!
@problem trivial_connected
@title The Two Extremes
@concept connected_examples

@preamble
The codiscrete topology has two open sets and no others, so a set both open and closed is already one of the two the definition allows. Nothing is left to check: the hypothesis is the conclusion.

The discrete topology is the other extreme. On the two-point set `Bool` the set `{true}` is open, and so is its complement, so `{true}` is both open and closed while being neither empty nor everything. A discrete space with two distinct points is never connected, and this is the smallest witness.
@description
Show `codiscrete_isConnected` and `discrete_bool_not_isConnected`. The first is one of its own hypotheses. For the second, `singleton_true_not_trivial` from the section on homeomorphisms is the fact that `{true}` is neither `∅` nor `Set.univ`, and `trivial` proves whatever the discrete topology asks.
-/
theorem codiscrete_isConnected (X : Type u) : (codiscrete X).IsConnected :=
  fun _ hS _ => hS

theorem discrete_bool_not_isConnected : ¬ (discrete Bool).IsConnected := fun h =>
  singleton_true_not_trivial (h {true} trivial trivial)

/-! @end -/

/-!
@problem define_interval
@title Intervals
@concept connected_examples

@preamble
A set of reals is an *interval* when it omits no point lying between two of its own: if `x` and `y` belong to it and `x < r < y`, then `r` belongs to it. Open, closed and half-open intervals all satisfy this, bounded or not, and so do the empty set, a single point and the whole line. The condition names the shape and says nothing about endpoints.

Because it says nothing about them, the weak form has to be deduced. If `x ≤ r ≤ y` with `x` and `y` in the set, then `r` is in it: the two cases where an inequality is an equality are the cases where `r` is one of the two points already.
@description
Define `IsInterval`, quantified as `∀ x ∈ S, ∀ y ∈ S, ∀ r, x < r → r < y → r ∈ S`, and prove `IsInterval.mem_of_le`. `eq_or_lt_of_le` splits a weak inequality into the two cases and `rcases … with rfl | hlt` substitutes in the first.
-/

def IsInterval (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ r, x < r → r < y → r ∈ S

theorem IsInterval.mem_of_le {S : Set ℝ} (h : IsInterval S) {a b x : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (h1 : a ≤ x) (h2 : x ≤ b) : x ∈ S := by
  rcases eq_or_lt_of_le h1 with rfl | hlt
  · exact ha
  rcases eq_or_lt_of_le h2 with rfl | hlt2
  · exact hb
  exact h a ha b hb x hlt hlt2

/-- @spec -/
example (S : Set ℝ) : IsInterval S ↔ ∀ x ∈ S, ∀ y ∈ S, ∀ r, x < r → r < y → r ∈ S := Iff.rfl

/-! @end -/

/-!
@problem line_reach
@title Reaching Out from a Point of an Open Set
@concept connected_examples

@preamble
An open set of the line holds a ball about each of its points, and a ball about `c` is an interval around it: `y ∈ line.ball c ε` says `|c - y| < ε`, which `abs_lt` splits into the two inequalities bounding `y` on either side. Two consequences of that are what any argument approaching a point from one side wants.

Rightwards: if `c` lies in an open `U` and `c < b`, then `U` holds a point strictly to the right of `c` and no further out than `b`. Half the radius gives a candidate, and the smaller of it and `b` stays in range.

Leftwards: if `c` lies in an open `V`, then for some positive `ε` every point of the stretch `c - ε < y ≤ c` lies in `V`.
@description
Prove `line_open_right` and `line_open_left`. `hU c hc` produces the radius and the containment; `lt_min` and `min_le_left` handle the smaller of two candidates, and `show |c - y| < ε` restates the membership in the ball as the inequality `abs_lt` splits.
-/

theorem line_open_right {U : Set ℝ} (hU : line.toTopology.IsOpen U) {c : ℝ} (hc : c ∈ U)
    {b : ℝ} (hcb : c < b) : ∃ x, c < x ∧ x ≤ b ∧ x ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := hU c hc
  have h1 : c < min (c + ε / 2) b := lt_min (by linarith) hcb
  have h2 : min (c + ε / 2) b ≤ c + ε / 2 := min_le_left _ _
  refine ⟨min (c + ε / 2) b, h1, min_le_right _ _, hsub ?_⟩
  show |c - min (c + ε / 2) b| < ε
  rw [abs_lt]
  constructor <;> linarith

theorem line_open_left {V : Set ℝ} (hV : line.toTopology.IsOpen V) {c : ℝ} (hc : c ∈ V) :
    ∃ ε > 0, ∀ y, c - ε < y → y ≤ c → y ∈ V := by
  obtain ⟨ε, hε, hsub⟩ := hV c hc
  refine ⟨ε, hε, fun y h1 h2 => hsub ?_⟩
  show |c - y| < ε
  rw [abs_lt]
  constructor <;> linarith

/-! @end -/

/--
@problem line_no_split
@title The Supremum of the Points Reached
@concept connected_examples

@preamble
Here is the argument that keeps the line in one piece, and the least upper bound property is what does the work.

Let `S` be an interval, let `U` and `V` be open sets covering it and sharing none of its points, and suppose `a ∈ S` lies in `U` and `b ∈ S` lies in `V`, with `a < b`. Collect the points of `[a, b]` that lie in `U`. That set holds `a`, and `b` bounds it above, so it has a least upper bound `c`; and `c` lies between `a` and `b`, hence in `S`.

Now `c` cannot lie in `U`. It would fall short of `b`, which lies in `V`, and then `U` would reach past `c` — a point no upper bound of the set allows. So `c` lies in `V`, and `V` holds a whole stretch to the left of `c`. But a least upper bound is approached from within, so that stretch holds a point of the set: a point of `S` lying in `U` and in `V` at once, which the hypotheses forbid.
@description
Prove `line_no_split`: those hypotheses are contradictory. `Real.exists_isLUB` supplies `c` from the nonemptiness and the bound; `hlub.1` is the upper-bound half, `hlub.2` the least half, and `hlub.exists_between` produces a member of the set above `c - ε`.
-/
theorem line_no_split {S U V : Set ℝ} (h : IsInterval S) (hU : line.toTopology.IsOpen U)
    (hV : line.toTopology.IsOpen V) (hno : ∀ x ∈ S, x ∈ U → x ∉ V) (hcov : S ⊆ U ∪ V)
    {a b : ℝ} (haS : a ∈ S) (hbS : b ∈ S) (haU : a ∈ U) (hbV : b ∈ V) (hab : a < b) : False := by
  obtain ⟨c, hlub⟩ := Real.exists_isLUB (s := {x | a ≤ x ∧ x ≤ b ∧ x ∈ U})
    ⟨a, le_refl a, hab.le, haU⟩ ⟨b, fun x hx => hx.2.1⟩
  have hac : a ≤ c := hlub.1 ⟨le_refl a, hab.le, haU⟩
  have hcb : c ≤ b := hlub.2 (fun x hx => hx.2.1)
  have hcS : c ∈ S := IsInterval.mem_of_le h haS hbS hac hcb
  have hcU : c ∉ U := fun hcU => by
    obtain ⟨x, hcx, hxb, hxU⟩ :=
      line_open_right hU hcU (lt_of_le_of_ne hcb fun e => hno c hcS hcU (e ▸ hbV))
    exact absurd (hlub.1 ⟨hac.trans hcx.le, hxb, hxU⟩) (not_le.mpr hcx)
  obtain ⟨ε, hε, hball⟩ := line_open_left hV ((hcov hcS).resolve_left hcU)
  obtain ⟨x, hxA, hxgt, hxle⟩ := hlub.exists_between (show c - ε < c by linarith)
  exact hno x (IsInterval.mem_of_le h haS hbS hxA.1 hxA.2.1) hxA.2.2 (hball x hxgt hxle)

/-!
@problem interval_connected
@title An Interval is Connected
@concept connected_examples

@preamble
Suppose two open sets divide an interval `S`. Then some point of `S` escapes the first and some point escapes the second, and each of the two lies in the set the other escaped, since together they cover `S`. The two points are distinct, one being in the first set and the other not, so one lies to the left of the other — and either way the previous problem forbids it. Only the order of the two sets changes between the cases.

Two consequences follow at once. Every set `{x | a ≤ x ∧ x ≤ b}` is an interval, so every closed interval is connected; and `unitInterval` is such a set.
@description
Prove `line_isConnectedSet_of_isInterval`, then `line_isConnectedSet_segment` and `unitInterval_isConnectedSet`. `by_contra` and `push Not` turn the goal into the two escaping points, `Set.not_subset` names them, and `Or.resolve_left` puts each into the set the other escaped.
-/

theorem line_isConnectedSet_of_isInterval {S : Set ℝ} (h : IsInterval S) :
    line.toTopology.IsConnectedSet S := by
  intro U V hU hV hno hcov
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haS, haU⟩ := Set.not_subset.mp hcon.1
  obtain ⟨b, hbS, hbV⟩ := Set.not_subset.mp hcon.2
  have haV : a ∈ V := (hcov haS).resolve_left haU
  have hbU : b ∈ U := (hcov hbS).resolve_right hbV
  rcases lt_or_gt_of_ne (fun e : a = b => haU (e ▸ hbU)) with hlt | hgt
  · exact line_no_split h hV hU (fun x h1 h2 h3 => hno x h1 h3 h2)
      (fun x hx => (hcov hx).symm) haS hbS haV hbU hlt
  · exact line_no_split h hU hV hno hcov hbS haS hbU haV hgt

theorem line_isConnectedSet_segment (a b : ℝ) :
    line.toTopology.IsConnectedSet {x | a ≤ x ∧ x ≤ b} :=
  line_isConnectedSet_of_isInterval
    (fun _ hx _ hy _ h1 h2 => ⟨le_trans hx.1 h1.le, le_trans h2.le hy.2⟩)

theorem unitInterval_isConnectedSet : line.toTopology.IsConnectedSet unitInterval :=
  line_isConnectedSet_segment 0 1

/-! @end -/

/-!
@concept connected_images
@title Connectedness Under Continuous Maps
@kind theorem

A continuous map cannot tear a space apart, so it carries a connected set to a connected set: any division of the image pulls back to a division of the source. Connectedness is therefore a property of the space and not of the way it is presented, and on the line the theorem is the intermediate value theorem of calculus.
-/

/--
@problem image_connected
@title The Continuous Image of a Connected Set
@concept connected_images

@preamble
Let `f` be continuous and let `S` be connected. Suppose two open sets cover `f '' S` and share none of its points. Their preimages are open, they cover `S`, and no point of `S` lies in both — every hypothesis is inherited by taking preimages, because a point of `S` lies in the preimage of a set exactly when its image lies in the set.

So `S` lies inside one of the preimages, and its image lies inside the corresponding set.
@description
Prove `Topology.isConnectedSet_image`. Each hypothesis for the preimages is one line, since a point of `f '' S` is `⟨x, hx, rfl⟩`; `Set.image_subset_iff` trades the image on the left of a containment for a preimage on the right.
-/
theorem Topology.isConnectedSet_image {X : Type u} {Y : Type v} (T : Topology X)
    {T' : Topology Y} {f : X → Y} (hf : T.Continuous T' f) {S : Set X}
    (hS : T.IsConnectedSet S) : T'.IsConnectedSet (f '' S) := by
  intro U V hU hV hno hcov
  rcases hS (f ⁻¹' U) (f ⁻¹' V) (hf U hU) (hf V hV)
      (fun x hx => hno (f x) ⟨x, hx, rfl⟩) (fun x hx => hcov ⟨x, hx, rfl⟩) with h0 | h0
  · exact Or.inl (Set.image_subset_iff.mpr h0)
  · exact Or.inr (Set.image_subset_iff.mpr h0)

/--
@problem homeomorphic_connected
@title Connectedness is a Topological Property
@concept connected_images

@preamble
Homeomorphic spaces are the same space as far as a topology can tell, so a property stated with open sets alone passes from either to the other. Connectedness is such a property.

Let `e` carry `T` to `T'`, and let `V` be open and closed in `T'`. Its preimage along `e.toFun` is open and closed in `T`, since `e.isOpen_iff` reads openness on either side of the map and taking preimages commutes with complements. So the preimage is empty or everything — and `V` is the preimage of its preimage, which settles which.
@description
Show `Homeomorphic.isConnected`. `obtain ⟨e⟩` opens the existence of a homeomorphism; `Set.preimage_compl` moves a complement across a preimage, and `rw [← e.preimage_preimage V, h0]` rewrites `V` as a preimage of what has just been identified.
-/
theorem Homeomorphic.isConnected {X : Type u} {Y : Type v} {T : Topology X} {T' : Topology Y}
    (h : Homeomorphic T T') (hT : T.IsConnected) : T'.IsConnected := by
  obtain ⟨e⟩ := h
  intro V hVo hVc
  have hc : T.IsClosed (e.toFun ⁻¹' V) := by
    show T.IsOpen _
    rw [← Set.preimage_compl]
    exact (Homeomorphism.isOpen_iff e Vᶜ).mp hVc
  rcases hT (e.toFun ⁻¹' V) ((Homeomorphism.isOpen_iff e V).mp hVo) hc with h0 | h0
  · left
    rw [← Homeomorphism.preimage_preimage e V, h0, Set.preimage_empty]
  · right
    rw [← Homeomorphism.preimage_preimage e V, h0, Set.preimage_univ]

/-!
@problem line_open_rays
@title The Open Rays
@concept connected_images

@preamble
The sets `{y | y < c}` and `{y | c < y}` are open in the line. A point `x` below `c` has the room `c - x` beneath it, and any `y` within that distance of `x` is still below `c`; the other ray is the mirror image.
@description
Prove `line_isOpen_lt` and `line_isOpen_gt`. Restate the hypothesis with `have hx' : x < c := hx`, offer the radius, and turn the membership in the ball into `|x - y| < c - x`, which `abs_lt` splits and `linarith` finishes.
-/

theorem line_isOpen_lt (c : ℝ) : line.toTopology.IsOpen {y | y < c} := by
  intro x hx
  have hx' : x < c := hx
  refine ⟨c - x, by linarith, fun y hy => ?_⟩
  have h : |x - y| < c - x := hy
  rw [abs_lt] at h
  show y < c
  linarith [h.1]

theorem line_isOpen_gt (c : ℝ) : line.toTopology.IsOpen {y | c < y} := by
  intro x hx
  have hx' : c < x := hx
  refine ⟨x - c, by linarith, fun y hy => ?_⟩
  have h : |x - y| < x - c := hy
  rw [abs_lt] at h
  show c < y
  linarith [h.2]

/-! @end -/

/--
@problem intermediate_value
@title The Intermediate Value Theorem
@concept connected_images

@preamble
A continuous real function on `[a, b]` takes every value between `f a` and `f b`. The classical proof builds the point by repeated bisection; the topological proof observes that the point is already there.

Suppose `c` lies between the two values and is never taken. The preimages of the two open rays below and above `c` are then open, they cover `[a, b]` — every value is below or above `c`, never equal to it — and they share no point of it. Since the interval is connected, one of them holds all of it: either every value is below `c`, and `f b` is not, or every value is above `c`, and `f a` is not.
@description
Prove `line_intermediate_value`. `by_contra` and `push Not` give the assumption that the value is never taken, `lt_trichotomy` splits a value against `c`, and `exacts` closes the three cases in one line.
-/
theorem line_intermediate_value {f : ℝ → ℝ} (hf : line.toTopology.Continuous line.toTopology f)
    {a b c : ℝ} (hab : a ≤ b) (h1 : f a < c) (h2 : c < f b) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c := by
  by_contra hcon
  push Not at hcon
  have hcov : {x | a ≤ x ∧ x ≤ b} ⊆ f ⁻¹' {y | y < c} ∪ f ⁻¹' {y | c < y} := by
    intro x hx
    rcases lt_trichotomy (f x) c with h | h | h
    exacts [Or.inl h, absurd h (hcon x hx.1 hx.2), Or.inr h]
  have hno : ∀ x ∈ {x | a ≤ x ∧ x ≤ b}, x ∈ f ⁻¹' {y | y < c} → x ∉ f ⁻¹' {y | c < y} := by
    intro x _ hlt hgt
    exact absurd (show f x < c from hlt) (not_lt.mpr (le_of_lt (show c < f x from hgt)))
  rcases line_isConnectedSet_segment a b _ _ (hf _ (line_isOpen_lt c)) (hf _ (line_isOpen_gt c))
      hno hcov with h0 | h0
  · exact absurd (h0 ⟨hab, le_refl b⟩) (not_lt.mpr h2.le)
  · exact absurd (h0 ⟨le_refl a, hab⟩) (not_lt.mpr h1.le)

/-!
@concept components
@title Connected Components
@kind definition

A space that is not connected still decomposes. Each point lies in a largest connected set, its component; the components cover the space and never overlap in part, and each of them is closed, since the closure of a connected set is connected. At the far end from a connected space is one whose components are single points.
-/

/-!
@problem union_connected
@title Unions of Connected Sets Through a Point
@concept components

@preamble
A single point is connected: whichever of the two sets catches it catches the whole of `{x}`.

Now take a family of connected sets, every one of them containing a point `p`, and let two open sets cover the union and share none of its points. Each member of the family is covered by the two as well and shares none of its points with them, so each member lies inside one of the two. Say `p` lies in the first. A member lying inside the second would put `p` in both, so every member lies inside the first, and so does the union. If `p` lies in the second instead, the same argument runs with the sides exchanged.
@description
Prove `Topology.isConnectedSet_singleton` and `Topology.isConnectedSet_sUnion`, the second for a family `F` all of whose members contain `p`. A membership `y ∈ {x}` is the equation `y = x` and must be restated as one before rewriting; `by_cases hpU : p ∈ U` chooses the side, and `rintro x ⟨S, hSF, hxS⟩` opens a point of `⋃₀ F`.
-/

theorem Topology.isConnectedSet_singleton {X : Type u} (T : Topology X) (x : X) :
    T.IsConnectedSet {x} := by
  intro U V _ _ _ hcov
  have hx : x ∈ ({x} : Set X) := rfl
  rcases hcov hx with h | h
  · refine Or.inl fun y hy => ?_
    have e : y = x := hy
    rw [e]
    exact h
  · refine Or.inr fun y hy => ?_
    have e : y = x := hy
    rw [e]
    exact h

theorem Topology.isConnectedSet_sUnion {X : Type u} (T : Topology X) {F : Set (Set X)} {p : X}
    (hp : ∀ S ∈ F, p ∈ S) (h : ∀ S ∈ F, T.IsConnectedSet S) : T.IsConnectedSet (⋃₀ F) := by
  intro U V hU hV hno hcov
  have key : ∀ S ∈ F, S ⊆ U ∨ S ⊆ V := fun S hSF => h S hSF U V hU hV
    (fun x hx => hno x ⟨S, hSF, hx⟩) (fun x hx => hcov ⟨S, hSF, hx⟩)
  by_cases hpU : p ∈ U
  · left
    rintro x ⟨S, hSF, hxS⟩
    rcases key S hSF with hs | hs
    · exact hs hxS
    · exact (hno p ⟨S, hSF, hp S hSF⟩ hpU (hs (hp S hSF))).elim
  · right
    rintro x ⟨S, hSF, hxS⟩
    rcases key S hSF with hs | hs
    · exact absurd (hs (hp S hSF)) hpU
    · exact hs hxS

/-! @end -/

/-!
@problem define_component
@title The Component of a Point
@concept components

@preamble
The *connected component* of `x` is the union of every connected set that contains `x`. All of those sets pass through `x`, so the union is connected by the problem just proved, and nothing connected containing `x` lies outside it: it is the largest connected set around `x`.

The point itself belongs to it, since `{x}` is one of the sets united.
@description
Define `Topology.component`, the union `⋃₀ {S | T.IsConnectedSet S ∧ x ∈ S}`, and prove `Topology.mem_component`. The witness for the second is the singleton, whose connectedness is the previous problem and whose two memberships are `rfl`.
-/

def Topology.component {X : Type u} (T : Topology X) (x : X) : Set X :=
  ⋃₀ {S | T.IsConnectedSet S ∧ x ∈ S}

theorem Topology.mem_component {X : Type u} (T : Topology X) (x : X) : x ∈ T.component x :=
  ⟨{x}, ⟨Topology.isConnectedSet_singleton T x, rfl⟩, rfl⟩

/-- @spec -/
example (X : Type) (T : Topology X) (x y : X) :
    y ∈ T.component x ↔ ∃ S, (T.IsConnectedSet S ∧ x ∈ S) ∧ y ∈ S := Iff.rfl

/-! @end -/

/-!
@problem component_maximal
@title Components are Maximal, and Do Not Overlap
@concept components

@preamble
Three statements say what a component is, and each is a line.

It is connected, being a union of connected sets through `x`. It contains every connected set containing `x`, being the union of them. And two components that meet are equal: if `y` lies in the component of `x`, then the component of `x` is a connected set containing `y`, so it lies inside the component of `y`; that carries `x` into the component of `y`, which then lies inside the component of `x` for the same reason.

So the components partition the space. Every point has one, and two of them are equal or share no point at all.
@description
Prove `Topology.isConnectedSet_component`, `Topology.subset_component` and `Topology.component_eq_of_mem`. The first two are the union lemma and the definition read back; the third is `Set.Subset.antisymm` on the two containments the second supplies.
-/

theorem Topology.isConnectedSet_component {X : Type u} (T : Topology X) (x : X) :
    T.IsConnectedSet (T.component x) :=
  Topology.isConnectedSet_sUnion T (fun _ hS => hS.2) (fun _ hS => hS.1)

theorem Topology.subset_component {X : Type u} (T : Topology X) {S : Set X} {x : X}
    (hS : T.IsConnectedSet S) (hx : x ∈ S) : S ⊆ T.component x :=
  fun _ hy => ⟨S, ⟨hS, hx⟩, hy⟩

theorem Topology.component_eq_of_mem {X : Type u} (T : Topology X) {x y : X}
    (h : y ∈ T.component x) : T.component y = T.component x := by
  have h1 : T.component x ⊆ T.component y :=
    Topology.subset_component T (Topology.isConnectedSet_component T x) h
  have hx : x ∈ T.component y := h1 (Topology.mem_component T x)
  exact Set.Subset.antisymm
    (Topology.subset_component T (Topology.isConnectedSet_component T y) hx) h1

/-! @end -/

/-!
@problem component_closed
@title Components are Closed
@concept components

@preamble
The closure of a connected set is connected. Let two open sets cover `T.closure S` and share none of its points. They cover `S` as well and share none of its points, so `S` lies inside one of them, say the first. Then `S` meets the second nowhere, so `S` lies inside the complement of the second, which is closed; and a closed set containing `S` contains its closure. Every point of the closure is thus outside the second set and so, by the cover, inside the first.

A component is then closed. Its closure is a connected set containing the point, so the closure lies back inside the component, and a set containing its own closure is closed.
@description
Prove `Topology.isConnectedSet_closure` and `Topology.isClosed_component`. `T.closure_min` wants the complement's closedness, which is `show T.IsOpen _` and then `rwa [compl_compl]`; `Or.resolve_right` turns the cover into a membership, and `T.isClosed_iff_closure_eq` reduces the second claim to two containments.
-/

theorem Topology.isConnectedSet_closure {X : Type u} (T : Topology X) {S : Set X}
    (hS : T.IsConnectedSet S) : T.IsConnectedSet (T.closure S) := by
  intro U V hU hV hno hcov
  have hsub := Topology.subset_closure T S
  have hVc : T.IsClosed Vᶜ := by show T.IsOpen _; rwa [compl_compl]
  have hUc : T.IsClosed Uᶜ := by show T.IsOpen _; rwa [compl_compl]
  rcases hS U V hU hV (fun x hx => hno x (hsub hx)) (fun x hx => hcov (hsub hx)) with hs | hs
  · have hc : T.closure S ⊆ Vᶜ :=
      Topology.closure_min T hVc (fun z hz => hno z (hsub hz) (hs hz))
    exact Or.inl fun x hx => (hcov hx).resolve_right (hc hx)
  · have hc : T.closure S ⊆ Uᶜ :=
      Topology.closure_min T hUc (fun z hz hzU => hno z (hsub hz) hzU (hs hz))
    exact Or.inr fun x hx => (hcov hx).resolve_left (hc hx)

theorem Topology.isClosed_component {X : Type u} (T : Topology X) (x : X) :
    T.IsClosed (T.component x) := by
  rw [Topology.isClosed_iff_closure_eq T]
  refine Set.Subset.antisymm ?_ (Topology.subset_closure T _)
  exact Topology.subset_component T
    (Topology.isConnectedSet_closure T (Topology.isConnectedSet_component T x))
    (Topology.subset_closure T _ (Topology.mem_component T x))

/-! @end -/

/-!
@problem totally_disconnected
@title Totally Disconnected Spaces
@concept components

@preamble
A space whose components are as small as they can be — every component a single point — is *totally disconnected*. The rationals with the distance they inherit from the line are the interesting example — between any two of them lies an irrational number to cut at — and a discrete space is the plain one.

In a discrete space let `S` be connected and contain `x`. The sets `{x}` and its complement are open, they cover `S` and they share no point of it, so `S` lies inside one of them; not inside the second, which leaves `x` out. So `S ⊆ {x}`, every connected set through `x` is `{x}` or empty, and the component of `x` is `{x}`.
@description
Define `Topology.IsTotallyDisconnected`, which says that `T.component x = {x}` for every `x`, and prove `discrete_isTotallyDisconnected`. `Set.Subset.antisymm` splits the equality of sets; `trivial` proves openness in a discrete space, and `Set.union_compl_self` rewrites the cover to `Set.univ`.
-/

def Topology.IsTotallyDisconnected {X : Type u} (T : Topology X) : Prop :=
  ∀ x, T.component x = {x}

theorem discrete_isTotallyDisconnected (X : Type u) : (discrete X).IsTotallyDisconnected := by
  intro x
  apply Set.Subset.antisymm
  · rintro y ⟨S, ⟨hS, hxS⟩, hyS⟩
    have hcov : S ⊆ {x} ∪ {x}ᶜ := by rw [Set.union_compl_self]; exact Set.subset_univ S
    rcases hS {x} {x}ᶜ trivial trivial (fun _ _ h1 h2 => h2 h1) hcov with hs | hs
    · exact hs hyS
    · exact absurd (hs hxS) (fun hc => hc rfl)
  · intro y hy
    have e : y = x := hy
    rw [e]
    exact Topology.mem_component _ x

/-- @spec -/
example (X : Type) (T : Topology X) :
    T.IsTotallyDisconnected ↔ ∀ x, T.component x = {x} := Iff.rfl

/-! @end -/

/-!
@concept path_connected
@title Paths
@kind definition

The everyday reason for believing a space to be in one piece is that one can walk across it. A path is a continuous map from the unit interval into the space, and a space is path-connected when every two of its points are joined by one. Since the interval is connected, so is every space that is — and the walk is usually the easier thing to exhibit.
-/

/-!
@problem define_path_connected
@title Paths and Path-Connected Spaces
@concept path_connected

@preamble
The unit interval carries the topology it inherits from the line, and a *path* in a space `X` is a continuous map from the interval into `X`. Its endpoints are its values at the two ends of the interval, which as points of the subspace are the numbers with their memberships attached: `unitInterval.zero` and `unitInterval.one` are given below.

A space is *path-connected* when any two of its points are the endpoints of a path, the first point at the start.
@description
Define `Topology.IsPathConnected`: for all `x y : X` there is a `γ : unitInterval → X` which is continuous from `line.toTopology.subspace unitInterval` to `T`, with `γ unitInterval.zero = x` and `γ unitInterval.one = y`, the three conditions in that order.
-/

/-- @given -/
def unitInterval.zero : unitInterval := ⟨0, le_refl 0, by norm_num⟩

/-- @given -/
def unitInterval.one : unitInterval := ⟨1, by norm_num, le_refl 1⟩

def Topology.IsPathConnected {X : Type u} (T : Topology X) : Prop :=
  ∀ x y : X, ∃ γ : unitInterval → X,
    (line.toTopology.subspace unitInterval).Continuous T γ ∧
      γ unitInterval.zero = x ∧ γ unitInterval.one = y

/-- @spec -/
example (X : Type) (T : Topology X) :
    T.IsPathConnected ↔ ∀ x y : X, ∃ γ : unitInterval → X,
      (line.toTopology.subspace unitInterval).Continuous T γ ∧
        γ unitInterval.zero = x ∧ γ unitInterval.one = y := Iff.rfl

/-! @end -/

/--
@problem line_path_connected
@title The Line is Path-Connected
@concept path_connected

@preamble
Between two reals runs the straight path `t ↦ (y - x) t + x`, which is at `x` when `t` is `0` and at `y` when `t` is `1`. Restricted to the unit interval it is a path from the first point to the second.

Its continuity is the affine map's, composed with the inclusion of the subspace in the line. One case has to be taken apart: the affine map's continuity was proved for a nonzero slope, so when `x` and `y` are the same point the path is a constant map and is continuous for that reason instead.
@description
Prove `line_isPathConnected`. Offer `fun p => (y - x) * p.val + x`; `by_cases h : y - x = 0` splits the two cases, `funext` and `ring` identify the map with a constant in the first, and `show` restates each endpoint as the arithmetic that `ring` closes.
-/
theorem line_isPathConnected : line.toTopology.IsPathConnected := by
  intro x y
  refine ⟨fun p => (y - x) * p.val + x, ?_, ?_, ?_⟩
  · by_cases h : y - x = 0
    · have he : (fun p : unitInterval => (y - x) * p.val + x) = fun _ => x := by
        funext p; rw [h]; ring
      rw [he]
      exact Topology.continuous_const _ line.toTopology x
    · exact Topology.continuous_comp _
        (Topology.continuous_subspace_val line.toTopology unitInterval)
        (line_continuous_affine_top (y - x) x h)
  · show (y - x) * 0 + x = x
    ring
  · show (y - x) * 1 + x = y
    ring

/--
@problem path_connected_connected
@title A Path-Connected Space is Connected
@concept path_connected

@preamble
Suppose a space is path-connected and yet has a set `S` both open and closed which is neither empty nor everything. Take a point `x` in `S`, a point `y` outside it, and a path from the one to the other.

The preimage of `S` along the path is open and closed in the unit interval, which is a connected space: the interval is a connected set, and a connected set is a connected space. So the preimage is empty or the whole interval. It is not empty, since the path starts inside `S`; and it is not everything, since the path ends outside `S`. The space has no such `S`, and is connected.
@description
Prove `Topology.isConnected_of_isPathConnected`. `push Not` turns the denial of the disjunction into a nonempty `S` and, with `Set.ne_univ_iff_exists_notMem`, a point outside it; `Topology.continuous_iff_closed` gives the closedness of the preimage, and `Set.mem_preimage` with the endpoint equations places the two ends of the path.
-/
theorem Topology.isConnected_of_isPathConnected {X : Type u} {T : Topology X}
    (h : T.IsPathConnected) : T.IsConnected := by
  intro S hSo hSc
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hcon.1
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem S).mp hcon.2
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := h x y
  have hI := Topology.isConnected_subspace line.toTopology unitInterval_isConnectedSet
  rcases hI (γ ⁻¹' S) (hγ S hSo) ((Topology.continuous_iff_closed _ T γ).mp hγ S hSc) with h0 | h0
  · have hm : unitInterval.zero ∈ γ ⁻¹' S := by rw [Set.mem_preimage, hγ0]; exact hx
    rw [h0] at hm
    exact hm
  · have hm : unitInterval.one ∈ γ ⁻¹' S := by rw [h0]; trivial
    rw [Set.mem_preimage, hγ1] at hm
    exact hy hm

end GeneralTopology
