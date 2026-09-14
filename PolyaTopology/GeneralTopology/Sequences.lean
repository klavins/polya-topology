import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import PolyaTopology.GeneralTopology.Connectedness

/-! @section Sequences and Convergence -/

universe u v

namespace GeneralTopology

/-!
@concept convergence
@title Convergence in a Metric Space
@kind definition

A sequence is a list of points running on for ever, and it converges to a point when its terms end up arbitrarily near that point. It is the oldest idea in analysis, and in a metric space it is stated with distances alone. What the rest of the section asks is how much of it survives when the distances are taken away.
-/

/-!
@problem define_convergence
@title The Limit of a Sequence
@concept convergence

@preamble
A *sequence* of points of a set `X` is a function `x : ℕ → X`, and its `n`-th term is `x n`. Nothing more is meant by the word: a sequence is a list of points indexed by the naturals, and it need not do anything in particular.

It converges to a point `a` when the terms end up arbitrarily near `a`. Fix a tolerance `ε > 0`. Past some index `k` every term is to be within `ε` of `a`, which is to say that `x n` lies in the ball of radius `ε` about `a` for all `n ≥ k`. The index may depend on the tolerance, and that dependence is the whole content: a smaller tolerance is allowed a longer wait.

A point `a` for which this holds is a *limit* of the sequence.
@description
Define `Metric.ConvergesTo`, taking a metric `M` on `X`, a sequence `x : ℕ → X` and a point `a`: for every `ε > 0` there is a `k : ℕ` with `M.dist a (x n) < ε` for every `n ≥ k`. Write the distance in that order, the limit first. Here `∀ n ≥ k, p n` abbreviates `∀ n, n ≥ k → p n`.
-/

def Metric.ConvergesTo {X : Type u} (M : Metric X) (x : ℕ → X) (a : X) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, M.dist a (x n) < ε

/-- @spec -/
example (X : Type) (M : Metric X) (x : ℕ → X) (a : X) :
    M.ConvergesTo x a ↔ ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, M.dist a (x n) < ε := Iff.rfl

/-! @end -/

/-!
@problem shrinking_reciprocals
@title The Reciprocals Shrink Below Any Bound
@concept convergence

@preamble
Every argument below that builds a sequence builds it out of a shrinking family of balls, and the radii it uses are the numbers `1 / (n + 1)`: positive for every natural `n`, and small for large ones. Both halves of that sentence have to be proved.

That the radius is positive is one division. That it eventually drops below a given `ε > 0` is the Archimedean property of the real line: no real number bounds every natural, so some `k` exceeds `1 / ε`, and past that `k` the reciprocal is below `ε`.
@description
Prove `one_div_succ_pos`, and then `exists_one_div_succ_lt`, which says that for `ε > 0` there is a `k` with `1 / (n + 1) < ε` for every `n ≥ k`. `exists_nat_gt` supplies the `k`, `Nat.cast_le` and `Nat.cast_nonneg` carry an inequality of naturals into the reals, and `div_lt_iff₀` clears a denominator so that `linarith` can finish.
-/

theorem one_div_succ_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact div_pos one_pos (by linarith)

theorem exists_one_div_succ_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ n ≥ k, 1 / ((n : ℝ) + 1) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨k, fun n hn => ?_⟩
  have h1 : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h3 : 1 / ε < (n : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
  rw [div_lt_iff₀ hε] at h3
  linarith

/-! @end -/

/-!
@problem simple_sequences
@title Two Sequences
@concept convergence

@preamble
The simplest sequence stands still. Every term of `fun _ => a` is `a` itself, the distance from `a` to it is zero, and any index at all will do: the constant sequence converges to its own value.

The simplest sequence that moves is `1 / (n + 1)` on the real line — one, a half, a third, and so on — and it converges to `0`. Here the index does depend on the tolerance, and the previous problem says which index answers which tolerance.
@description
Prove `Metric.convergesTo_const` and `line_convergesTo_zero`. In the first, `show` restates the goal as a distance from `a` to itself, which `Metric.dist_self` computes. In the second the distance is `|0 - 1 / (n + 1)|`; `zero_sub`, `abs_neg` and `abs_of_pos` strip it down to the number itself.
-/

theorem Metric.convergesTo_const {X : Type u} (M : Metric X) (a : X) :
    M.ConvergesTo (fun _ => a) a := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  show M.dist a a < ε
  rw [Metric.dist_self M]
  exact hε

theorem line_convergesTo_zero : line.ConvergesTo (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_one_div_succ_lt hε
  refine ⟨k, fun n hn => ?_⟩
  show |0 - 1 / ((n : ℝ) + 1)| < ε
  rw [zero_sub, abs_neg, abs_of_pos (one_div_succ_pos n)]
  exact hk n hn

/-! @end -/

/--
@problem limit_unique
@title A Sequence Has at Most One Limit
@concept convergence

@preamble
A sequence cannot approach two different points at once, and the triangle inequality is the reason.

Suppose `x` converges to `a` and to `b`, with `a ≠ b`, and let `d` be the distance between them, which is then positive. Past some index every term is within `d / 2` of `a`, and past some other index every term is within `d / 2` of `b`. Past both — the larger of the two indices will do — one single term is within `d / 2` of each. But then the journey from `a` to `b` through that term is shorter than `d`, and no journey from `a` to `b` is shorter than `d`.

So we may speak of *the* limit of a convergent sequence.
@description
Prove `Metric.convergesTo_unique`. `Metric.dist_pos` supplies the positive distance, `max k l` is an index past both, `le_max_left` and `le_max_right` place it, and `M.symm` turns one of the two distances around before `M.triangle` and `linarith` close the gap.
-/
theorem Metric.convergesTo_unique {X : Type u} (M : Metric X) {x : ℕ → X} {a b : X}
    (ha : M.ConvergesTo x a) (hb : M.ConvergesTo x b) : a = b := by
  by_contra hne
  have hd : 0 < M.dist a b := Metric.dist_pos M hne
  obtain ⟨k, hk⟩ := ha (M.dist a b / 2) (by linarith)
  obtain ⟨l, hl⟩ := hb (M.dist a b / 2) (by linarith)
  have h1 : M.dist a (x (max k l)) < M.dist a b / 2 := hk _ (le_max_left k l)
  have h2 : M.dist b (x (max k l)) < M.dist a b / 2 := hl _ (le_max_right k l)
  have h3 : M.dist (x (max k l)) b = M.dist b (x (max k l)) := M.symm
  have h4 := M.triangle a (x (max k l)) b
  linarith

/-!
@concept convergence_topological
@title Convergence Without Distances
@kind definition

A ball about the limit is only a way of saying *near the limit*, and a topology says that with neighbourhoods. Convergence therefore survives the loss of the metric, and where both readings can be had they agree. What does not survive is uniqueness: how many limits a sequence may have turns out to be a question about how well the space tells its points apart.
-/

/-!
@problem define_convergence_top
@title Convergence in a Topological Space
@concept convergence_topological

@preamble
Read the metric definition again with the balls hidden. A sequence converges to `a` when, for each way of saying *near `a`*, the terms are eventually there. In a topological space the ways of saying it are the neighbourhoods of `a`, and the definition is the same sentence with a neighbourhood `N` in place of the ball.

The constant sequence converges to its value here too, and for less reason than before: every neighbourhood of `a` contains `a`, so every term of the sequence is in it from the start.
@description
Define `Topology.ConvergesTo`, taking a topology `T` on `X`, a sequence `x : ℕ → X` and a point `a`: for every `N` with `T.IsNbhd a N` there is a `k : ℕ` with `x n ∈ N` for every `n ≥ k`. Then prove `Topology.convergesTo_const`, for which `rintro` takes the neighbourhood apart into the open set inside it.
-/

def Topology.ConvergesTo {X : Type u} (T : Topology X) (x : ℕ → X) (a : X) : Prop :=
  ∀ N, T.IsNbhd a N → ∃ k : ℕ, ∀ n ≥ k, x n ∈ N

theorem Topology.convergesTo_const {X : Type u} (T : Topology X) (a : X) :
    T.ConvergesTo (fun _ => a) a := by
  rintro N ⟨U, _, haU, hUN⟩
  exact ⟨0, fun _ _ => hUN haU⟩

/-- @spec -/
example (X : Type) (T : Topology X) (x : ℕ → X) (a : X) :
    T.ConvergesTo x a ↔ ∀ N, T.IsNbhd a N → ∃ k : ℕ, ∀ n ≥ k, x n ∈ N := Iff.rfl

/-! @end -/

/--
@problem convergence_bridge
@title The Two Definitions Agree
@concept convergence_topological

@preamble
In a metric space both definitions can be read, and they say the same thing — as the two definitions of continuity did, and for the same reason.

Forwards: a neighbourhood `N` of `a` holds an open set around `a`, and an open set of a metric space holds a ball about each of its points. Take the index that the ball's radius supplies, and every later term lies in the ball, hence in `N`.

Backwards: a ball about `a` is itself a neighbourhood of `a`, being open and containing its own centre. Apply the hypothesis to it and read off the index.
@description
Prove `Metric.convergesTo_iff`: `M.ConvergesTo x a` exactly when `M.toTopology.ConvergesTo x a`. Nothing needs rewriting in either direction, since a membership in a ball is the distance inequality it abbreviates. `Topology.nbhd_of_isOpen`, with `Metric.isOpenSet_ball` and `Metric.mem_ball_self`, makes a ball into a neighbourhood of its centre.
-/
theorem Metric.convergesTo_iff {X : Type u} (M : Metric X) (x : ℕ → X) (a : X) :
    M.ConvergesTo x a ↔ M.toTopology.ConvergesTo x a := by
  constructor
  · rintro h N ⟨U, hU, haU, hUN⟩
    obtain ⟨ε, hε, hball⟩ := hU a haU
    obtain ⟨k, hk⟩ := h ε hε
    exact ⟨k, fun n hn => hUN (hball (hk n hn))⟩
  · intro h ε hε
    obtain ⟨k, hk⟩ := h (Metric.ball M a ε)
      (Topology.nbhd_of_isOpen (Metric.toTopology M) (Metric.isOpenSet_ball M a ε)
        (Metric.mem_ball_self M a ε hε))
    exact ⟨k, fun n hn => hk n hn⟩

/--
@problem codiscrete_convergence
@title Where Every Sequence Converges to Everything
@concept convergence_topological

@preamble
The codiscrete topology has two open sets, and an open set containing a point is not the empty one, so it is the whole space. A neighbourhood of any point is therefore everything, and every term of every sequence is in it already.

So in a codiscrete space every sequence converges to every point at once, and a sequence has as many limits as the space has points. Uniqueness was a theorem about metric spaces, not a part of what convergence means.
@description
Prove `codiscrete_convergesTo`: every sequence in `codiscrete X` converges to every point of `X`. `rintro` opens the neighbourhood, and `rcases` on the openness of the set inside it gives the two cases, of which the empty one is refuted by `Set.notMem_empty`.
-/
theorem codiscrete_convergesTo {X : Type u} (x : ℕ → X) (a : X) :
    (codiscrete X).ConvergesTo x a := by
  rintro N ⟨U, hU, haU, hUN⟩
  refine ⟨0, fun n _ => hUN ?_⟩
  rcases hU with h | h
  · rw [h] at haU
    exact absurd haU (Set.notMem_empty a)
  · rw [h]
    trivial

/-!
@problem unique_limits
@title Unique Limits, Between T₁ and Hausdorff
@concept convergence_topological

@preamble
Which spaces have unique limits? Two conditions bracket the answer, and neither one is it.

A Hausdorff space has them. Two distinct limits are separated by disjoint open sets, each of which holds every term past some index; past both indices a single term lies in both, and the two sets share no point.

Conversely, a space with unique limits is T₁. Were it not, there would be distinct `x` and `y` with every open set containing `x` containing `y` as well. The constant sequence at `y` would then converge to `x` — every neighbourhood of `x` holds `y` — and to `y`, which is two limits.

Between the two conditions is a gap that nothing here closes: the converse of the first needs each point to have countably many neighbourhoods to work through, which a topology need not supply.
@description
Prove `Topology.convergesTo_unique` and `Topology.isT1_of_convergesTo_unique`. The first takes `max k l` as an index past both and rewrites along the emptiness of the intersection. In the second, `by_contra` and `push Not` turn the goal into the hypothesis that every open set around `x` holds `y`.
-/

theorem Topology.convergesTo_unique {X : Type u} {T : Topology X} (h : T.IsHausdorff)
    {x : ℕ → X} {a b : X} (ha : T.ConvergesTo x a) (hb : T.ConvergesTo x b) : a = b := by
  by_contra hne
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := h a b hne
  obtain ⟨k, hk⟩ := ha U (Topology.nbhd_of_isOpen T hU haU)
  obtain ⟨l, hl⟩ := hb V (Topology.nbhd_of_isOpen T hV hbV)
  have hm : x (max k l) ∈ U ∩ V := ⟨hk _ (le_max_left k l), hl _ (le_max_right k l)⟩
  rw [hUV] at hm
  exact Set.notMem_empty _ hm

theorem Topology.isT1_of_convergesTo_unique {X : Type u} {T : Topology X}
    (h : ∀ (x : ℕ → X) (a b : X), T.ConvergesTo x a → T.ConvergesTo x b → a = b) : T.IsT1 := by
  intro x y hxy
  by_contra hcon
  push Not at hcon
  have hconv : T.ConvergesTo (fun _ => y) x := by
    rintro N ⟨U, hU, hxU, hUN⟩
    exact ⟨0, fun _ _ => hUN (hcon U hU hxU)⟩
  exact hxy (h (fun _ => y) x y hconv (Topology.convergesTo_const T y))

/-! @end -/

/-!
@concept sequential_closure
@title Closures and Sequences
@kind theorem

In a metric space a point of the closure of a set is a point the set comes arbitrarily near, and a sequence is precisely a record of such an approach. So the closure can be described without open sets at all, and closedness becomes a condition on limits — which is the form in which analysis states it.
-/

/--
@problem sequential_closure
@title The Closure is Reached by Sequences
@concept sequential_closure

@preamble
A point lies in the closure of `S` when every ball about it meets `S`. Shrink the balls: for each `n` take a point of `S` inside the ball of radius `1 / (n + 1)`. Those points form a sequence in `S`, and it converges to the point, since the radii drop below any tolerance.

The other direction is the easy one. If a sequence in `S` converges to `a`, then each ball about `a` holds a term of the sequence, and that term is a point of `S` inside the ball.

Picking one point out of each of infinitely many nonempty sets is an appeal to choice, and Lean makes it with `Exists.choose`: for `h : ∃ y, p y`, the term `h.choose` is a witness and `h.choose_spec` is the proof that it is one.
@description
Prove `Metric.mem_closure_iff_seq`: `a ∈ M.toTopology.closure S` exactly when some sequence with every term in `S` converges to `a`. `Metric.mem_closure_iff` is the ball form of the closure, and a point of a ball is the distance inequality it abbreviates; name the family of witnesses in a `have` before choosing from it, so that the same term is chosen each time it is mentioned.
-/
theorem Metric.mem_closure_iff_seq {X : Type u} (M : Metric X) {S : Set X} {a : X} :
    a ∈ M.toTopology.closure S ↔ ∃ x : ℕ → X, (∀ n, x n ∈ S) ∧ M.ConvergesTo x a := by
  constructor
  · intro ha
    rw [Metric.mem_closure_iff M] at ha
    have hpt : ∀ n : ℕ, ∃ y, M.dist a y < 1 / ((n : ℝ) + 1) ∧ y ∈ S :=
      fun n => ha _ (one_div_succ_pos n)
    refine ⟨fun n => (hpt n).choose, fun n => (hpt n).choose_spec.2, ?_⟩
    intro ε hε
    obtain ⟨k, hk⟩ := exists_one_div_succ_lt hε
    exact ⟨k, fun n hn => lt_trans (hpt n).choose_spec.1 (hk n hn)⟩
  · rintro ⟨x, hxS, hconv⟩
    rw [Metric.mem_closure_iff M]
    intro ε hε
    obtain ⟨k, hk⟩ := hconv ε hε
    exact ⟨x k, hk k (le_refl k), hxS k⟩

/--
@problem sequentially_closed
@title Closed Means Closed Under Limits
@concept sequential_closure

@preamble
A set of a metric space is closed exactly when it contains the limit of every convergent sequence of its own points. That is what the word means in analysis, and here it is a corollary of the last problem.

A closed set is its own closure. So if a sequence in `S` converges to `a`, the last problem puts `a` in the closure, which is `S`.

Conversely, suppose `S` holds the limit of every convergent sequence in it. A point of the closure is the limit of such a sequence, so it lies in `S`; the closure is then contained in `S`, and a set containing its own closure is closed.
@description
Prove `Metric.isClosed_iff_seq`. `Topology.isClosed_iff_closure_eq` trades closedness for the equation `T.closure S = S`, and `Set.Subset.antisymm` splits that equation into two containments, of which `Topology.subset_closure` is one.
-/
theorem Metric.isClosed_iff_seq {X : Type u} (M : Metric X) (S : Set X) :
    M.toTopology.IsClosed S ↔
      ∀ (x : ℕ → X) (a : X), (∀ n, x n ∈ S) → M.ConvergesTo x a → a ∈ S := by
  rw [Topology.isClosed_iff_closure_eq (Metric.toTopology M) S]
  constructor
  · intro h x a hxS hconv
    rw [← h]
    exact (Metric.mem_closure_iff_seq M).mpr ⟨x, hxS, hconv⟩
  · intro h
    refine Set.Subset.antisymm ?_ (Topology.subset_closure (Metric.toTopology M) S)
    intro a ha
    obtain ⟨x, hxS, hconv⟩ := (Metric.mem_closure_iff_seq M).mp ha
    exact h x a hxS hconv

/-!
@concept sequential_continuity
@title Continuity and Limits
@kind theorem

A continuous map carries a convergent sequence to a convergent sequence — the behaviour the word *continuous* originally named. Between metric spaces the converse holds as well, so continuity may be tested one sequence at a time; between general spaces it may not, and the reason is the one that left the last concept's gap open.
-/

/-!
@problem continuous_limits
@title Continuous Maps Preserve Limits
@concept sequential_continuity

@preamble
If `x` converges to `a` and `f` is continuous, then the images `f (x n)` converge to `f a`. The proof is the definition of continuity at a point, read once.

Let `N` be a neighbourhood of `f a`. Continuity at `a` makes `f ⁻¹' N` a neighbourhood of `a`, so past some index every `x n` lies in it — which says that every `f (x n)` lies in `N`.

The same statement for metric spaces is this one carried across the bridge, and it is carried in both directions at once: the hypothesis is translated one way and the conclusion the other.
@description
Prove `Topology.convergesTo_comp`, and then `Metric.convergesTo_comp`. `Topology.continuous_iff_continuousAt` turns continuity into the statement at `a`; the metric version is the topological one with `Metric.convergesTo_iff` and `Metric.continuous_iff` applied on either side of it.
-/

theorem Topology.convergesTo_comp {X : Type u} {Y : Type v} (T : Topology X) {T' : Topology Y}
    {f : X → Y} (hf : T.Continuous T' f) {x : ℕ → X} {a : X} (h : T.ConvergesTo x a) :
    T'.ConvergesTo (fun n => f (x n)) (f a) := by
  intro N hN
  have hpre : T.IsNbhd a (f ⁻¹' N) :=
    (Topology.continuous_iff_continuousAt T T' f).mp hf a N hN
  obtain ⟨k, hk⟩ := h (f ⁻¹' N) hpre
  exact ⟨k, fun n hn => hk n hn⟩

theorem Metric.convergesTo_comp {X : Type u} {Y : Type v} (M : Metric X) (N : Metric Y)
    {f : X → Y} (hf : M.Continuous N f) {x : ℕ → X} {a : X} (h : M.ConvergesTo x a) :
    N.ConvergesTo (fun n => f (x n)) (f a) :=
  (Metric.convergesTo_iff N _ _).mpr
    (Topology.convergesTo_comp (Metric.toTopology M) ((Metric.continuous_iff M N f).mp hf)
      ((Metric.convergesTo_iff M x a).mp h))

/-! @end -/

/--
@problem seq_continuity_metric
@title Sequences Detect Continuity in a Metric Space
@concept sequential_continuity

@preamble
Between metric spaces the converse holds: a map that preserves the limit of every convergent sequence is continuous. The argument runs by contradiction, and it builds its sequence out of the failure it assumes.

Suppose `f` is not continuous at `a`. Then some `ε > 0` is missed by every `δ`: however small `δ` is, some point within `δ` of `a` has its image further than `ε` from `f a`. Take `δ = 1 / (n + 1)` for each `n` in turn and collect those points. They converge to `a`, since the radii shrink, so their images converge to `f a` by hypothesis — and yet every image is at least `ε` away from `f a`.
@description
Prove `Metric.continuous_of_seq`. `intro a ε hε` leaves a goal about `δ`; `by_contra` and `push Not` turn its denial into the family of bad points, out of which `Exists.choose` builds the sequence, and `not_lt` closes the contradiction at the end.
-/
theorem Metric.continuous_of_seq {X : Type u} {Y : Type v} (M : Metric X) (N : Metric Y)
    {f : X → Y}
    (h : ∀ (x : ℕ → X) (a : X), M.ConvergesTo x a → N.ConvergesTo (fun n => f (x n)) (f a)) :
    M.Continuous N f := by
  intro a ε hε
  by_contra hcon
  push Not at hcon
  have hpt : ∀ n : ℕ, ∃ y, M.dist a y < 1 / ((n : ℝ) + 1) ∧ ε ≤ N.dist (f a) (f y) :=
    fun n => hcon _ (one_div_succ_pos n)
  have hconv : M.ConvergesTo (fun n => (hpt n).choose) a := by
    intro δ hδ
    obtain ⟨k, hk⟩ := exists_one_div_succ_lt hδ
    exact ⟨k, fun n hn => lt_trans (hpt n).choose_spec.1 (hk n hn)⟩
  obtain ⟨k, hk⟩ := h _ a hconv ε hε
  exact absurd (hk k (le_refl k)) (not_lt.mpr (hpt k).choose_spec.2)

/-!
@concept cauchy_complete
@title Cauchy Sequences and Completeness
@kind definition

A sequence may bunch up with nothing to bunch up at: its terms grow arbitrarily close to one another while the point they would converge to is missing from the space. A space where that never happens is complete. It is the condition under which a limit may be asserted before it is known, and it is what the real numbers have that the rationals do not.
-/

/-!
@problem define_cauchy
@title Cauchy Sequences
@concept cauchy_complete

@preamble
Convergence names the limit. A sequence can be seen to be settling down without naming it, by the terms growing close to one another rather than to anything outside.

A sequence is *Cauchy* when for every tolerance `ε > 0` there is an index past which any two terms are within `ε` of each other. Two indices are quantified here, not one, and both are asked to be past the same `k`.

The condition mentions no point of the space but the terms themselves, and that is what makes it useful: it can be checked when the limit is not yet in hand, and even when there is none.
@description
Define `Metric.IsCauchy`, taking a metric `M` on `X` and a sequence `x : ℕ → X`: for every `ε > 0` there is a `k : ℕ` with `∀ m ≥ k, ∀ n ≥ k, M.dist (x m) (x n) < ε`, the two indices bound one after the other rather than together.
-/

def Metric.IsCauchy {X : Type u} (M : Metric X) (x : ℕ → X) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ m ≥ k, ∀ n ≥ k, M.dist (x m) (x n) < ε

/-- @spec -/
example (X : Type) (M : Metric X) (x : ℕ → X) :
    M.IsCauchy x ↔ ∀ ε > 0, ∃ k : ℕ, ∀ m ≥ k, ∀ n ≥ k, M.dist (x m) (x n) < ε := Iff.rfl

/-! @end -/

/--
@problem convergent_is_cauchy
@title Every Convergent Sequence is Cauchy
@concept cauchy_complete

@preamble
One implication holds in every metric space. If the terms are eventually all within `ε / 2` of the limit, then any two of them are within `ε` of each other, by the triangle inequality through the limit.

The halving is the whole of the trick, and it is the same halving that separated two points of a metric space by disjoint balls.

The converse is not a theorem. That a Cauchy sequence converges is a property a metric space may or may not have, and the next problems give it a name.
@description
Prove `Metric.isCauchy_of_convergesTo`. Apply the convergence at `ε / 2` and offer the index it returns; `M.symm` turns one of the two distances around before `M.triangle (x m) a (x n)` and `linarith` finish.
-/
theorem Metric.isCauchy_of_convergesTo {X : Type u} (M : Metric X) {x : ℕ → X} {a : X}
    (h : M.ConvergesTo x a) : M.IsCauchy x := by
  intro ε hε
  obtain ⟨k, hk⟩ := h (ε / 2) (by linarith)
  refine ⟨k, fun m hm n hn => ?_⟩
  have h1 : M.dist a (x m) < ε / 2 := hk m hm
  have h2 : M.dist a (x n) < ε / 2 := hk n hn
  have h3 : M.dist (x m) a = M.dist a (x m) := M.symm
  have h4 := M.triangle (x m) a (x n)
  linarith

/-!
@problem define_complete
@title Complete Metric Spaces
@concept cauchy_complete

@preamble
A metric space is *complete* when every Cauchy sequence in it converges — when the terms bunching together is enough to guarantee a point they bunch up at.

The rationals are not complete. A sequence of rationals may close in on a number that is irrational, and that number is not there to be its limit. The real line is complete, which is the reason it was built; that theorem rests on the least upper bound property, and it is not proved here.

Completeness is a property of the metric and not of the topology it induces. Two metrics may call exactly the same sets open while one of them is complete and the other is not.
@description
Define `Metric.IsComplete`, taking a metric `M` on `X`: for every sequence `x : ℕ → X` that is Cauchy there is a point `a` with `M.ConvergesTo x a`.
-/

def Metric.IsComplete {X : Type u} (M : Metric X) : Prop :=
  ∀ x : ℕ → X, M.IsCauchy x → ∃ a, M.ConvergesTo x a

/-- @spec -/
example (X : Type) (M : Metric X) :
    M.IsComplete ↔ ∀ x : ℕ → X, M.IsCauchy x → ∃ a, M.ConvergesTo x a := Iff.rfl

/-! @end -/

/-!
@problem define_discrete_metric
@title The Discrete Metric
@concept cauchy_complete

@preamble
Here is a metric that any set at all carries: a point is at distance `0` from itself, and at distance `1` from every other point. Writing it down calls for deciding whether two points are equal, which Lean asks for as the assumption `[DecidableEq X]`.

Symmetry and non-degeneracy are read off the two cases. The triangle inequality is read off a bound: the left-hand distance is at most `1`, and when the two outer points differ the right-hand sum is at least `1`, since one of its terms is. When the outer points agree the left-hand distance is `0` instead.

What every later proof uses is that the distance `1` is never beaten: two points less than `1` apart are the same point.
@description
Define `discreteMetric`, whose distance is `if x = y then 0 else 1` in that orientation, and prove `discreteMetric_eq_of_dist_lt_one`. `symm` and `eq_zero` bind their points implicitly and `triangle` takes its three explicitly, as `Metric` declares them. `by_cases` splits on an equality, `if_pos` and `if_neg` rewrite the branch it settles, and `split_ifs` does both at once where the value is only wanted between `0` and `1`.
-/

def discreteMetric (X : Type u) [DecidableEq X] : Metric X where
  dist x y := if x = y then 0 else 1
  symm {x y} := by
    by_cases h : x = y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  triangle x y z := by
    have hb : (0 : ℝ) ≤ if y = z then 0 else 1 := by split_ifs <;> norm_num
    have ha : (if x = z then (0 : ℝ) else 1) ≤ 1 := by split_ifs <;> norm_num
    by_cases h1 : x = y
    · subst h1
      rw [if_pos rfl, zero_add]
    · rw [if_neg h1]
      linarith
  eq_zero {x y} := by
    by_cases h : x = y
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]
      exact ⟨fun e => absurd e one_ne_zero, fun e => absurd e h⟩

theorem discreteMetric_eq_of_dist_lt_one {X : Type u} [DecidableEq X] {x y : X}
    (h : (discreteMetric X).dist x y < 1) : x = y := by
  by_contra hne
  have e : (discreteMetric X).dist x y = 1 := if_neg hne
  linarith

/-- @spec -/
example (X : Type) [DecidableEq X] (x y : X) :
    (discreteMetric X).dist x y = if x = y then 0 else 1 := rfl

/-! @end -/

/--
@problem discrete_metric_topology
@title The Discrete Metric Induces the Discrete Topology
@concept cauchy_complete

@preamble
The name is earned here. In this metric the ball of radius `1` about `x` holds `x` and nothing else, every other point being a whole unit away. So every set holds a ball about each of its own points, every set is open, and the topology the metric induces is the discrete one.

This is the first metric the subject has produced for a topology it wrote down by hand, and it settles a question left open when that topology was first met: the discrete topology does come from a distance.
@description
Prove `discreteMetric_toTopology`. `Topology.eq_of_isOpen_iff` reduces an equality of topologies to an equivalence between their open sets; one direction is `trivial`, and the other offers the radius `1` and closes with the fact from the previous problem.
-/
theorem discreteMetric_toTopology (X : Type u) [DecidableEq X] :
    (discreteMetric X).toTopology = discrete X := by
  apply Topology.eq_of_isOpen_iff
  intro U
  constructor
  · intro _
    trivial
  · intro _ x hx
    refine ⟨1, one_pos, fun y hy => ?_⟩
    have h1 : (discreteMetric X).dist x y < 1 := hy
    rw [← discreteMetric_eq_of_dist_lt_one h1]
    exact hx

/--
@problem discrete_metric_complete
@title The Discrete Metric is Complete
@concept cauchy_complete

@preamble
A Cauchy sequence in the discrete metric is eventually constant. Apply the condition at the tolerance `1`: past some index `k` any two terms are less than `1` apart, and in this metric that means they are equal. So every term past `k` is `x k` itself.

Such a sequence converges to `x k`, and at no cost: the distance from `x k` to every later term is `0`, which is below every tolerance. Every Cauchy sequence converges, so the space is complete.

The example is not a rich one — it is complete because it has so few Cauchy sequences to satisfy — but it is a space in which completeness can be settled outright.
@description
Prove `discreteMetric_isComplete`. Apply the Cauchy condition at `1`, offer `x k` as the limit and `k` as the index, and rewrite the two terms into one with the fact that a distance below `1` forces an equality.
-/
theorem discreteMetric_isComplete (X : Type u) [DecidableEq X] :
    (discreteMetric X).IsComplete := by
  intro x hx
  obtain ⟨k, hk⟩ := hx 1 one_pos
  refine ⟨x k, fun ε hε => ⟨k, fun n hn => ?_⟩⟩
  show (discreteMetric X).dist (x k) (x n) < ε
  rw [← discreteMetric_eq_of_dist_lt_one (hk k (le_refl k) n hn)]
  rw [Metric.dist_self (discreteMetric X)]
  exact hε

end GeneralTopology
