import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! @section Metric Spaces -/

universe u

namespace GeneralTopology

/-!
@concept metric_space
@title Metric Spaces
@kind definition

Distance is the first thing one measures about a pair of points, and a great deal of mathematics is an elaboration of it. A metric space is a set together with a rule that assigns to each pair of its points a real number, their distance, subject to three conditions taken from the way distance behaves on a map. Everything in this section is deduced from those three conditions and from nothing else.
-/

/-!
@problem define_metric
@title The Definition of a Metric Space
@concept metric_space

@preamble
What must a rule satisfy to deserve the name of a distance? Three things, and each of them holds for distance on a map.

The first is *symmetry*. The distance from `x` to `y` is the distance from `y` to `x`; a distance belongs to an unordered pair of points, not to a journey with a direction.

The second is the *triangle inequality*. Going from `x` to `z` by way of `y` is never shorter than going from `x` to `z` directly, so `d x z ≤ d x y + d y z`. The name comes from the plane, where it says that one side of a triangle is at most the sum of the other two.

The third is *non-degeneracy*. Two points are at distance zero exactly when they are the same point: `d x y = 0` if and only if `x = y`. Distinct points are held apart, and no point is held away from itself.

Notice what is not asked. Nothing here says that a distance is a non-negative number. It need not be asked, because it follows, as a problem below will show. One asks of a definition only what cannot be deduced.

A structure in Lean gathers data and the conditions on that data under a single name. A term of type `Metric X` is therefore a distance function on `X` together with proofs that it satisfies all three conditions, and the fields are named so that `M.dist x y` is the distance and `M.symm`, `M.triangle` and `M.eq_zero` are the three proofs.
@description
Define the structure `Metric X` for a type `X`, with four fields in this order: `dist`, of type `X → X → ℝ`; then `symm`, `triangle` and `eq_zero`, each quantified over all the points of `X` it mentions, carrying symmetry, the triangle inequality `dist x z ≤ dist x y + dist y z`, and the equivalence `dist x y = 0 ↔ x = y`.
-/

structure Metric (X : Type u) where
  dist : X → X → ℝ
  symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  eq_zero : ∀ x y, dist x y = 0 ↔ x = y

/-- @spec -/
example (X : Type) (M : Metric X) (x y z : X) :
    M.dist x y = M.dist y x
      ∧ M.dist x z ≤ M.dist x y + M.dist y z
      ∧ (M.dist x y = 0 ↔ x = y) :=
  ⟨M.symm x y, M.triangle x y z, M.eq_zero x y⟩

/-! @end -/

/--
@problem dist_self
@title The Distance From a Point to Itself
@concept metric_space

@preamble
Non-degeneracy is an equivalence, and each direction of it says something. Read from left to right it says that points at distance zero coincide, which is the substantial half. Read from right to left, and applied to the pair `x, x`, it says that the distance from a point to itself is zero.

Nothing is quantified away when a statement about all pairs is used on the pair `x, x`. The condition was stated for every `x` and every `y`, and `y` may be `x`.
@description
Show that `M.dist x x = 0`. If `h` is an equivalence then `h.mpr` is its right-to-left direction, and the equality it wants is `rfl`.
-/
theorem Metric.dist_self {X : Type u} (M : Metric X) (x : X) : M.dist x x = 0 :=
  (M.eq_zero x x).mpr rfl

/--
@problem dist_nonneg
@title Distances Are Never Negative
@concept metric_space

@preamble
A distance ought to be a non-negative number, and that was not among the conditions. It does not have to be, because the three conditions already force it.

Take two points `x` and `y`, and consider the journey from `x` back to `x` by way of `y`. The triangle inequality bounds the distance from `x` to itself by the length of that journey, which is `d x y + d y x`; the distance from `x` to itself is zero by the problem above; and `d y x` is `d x y` by symmetry. So `0 ≤ 2 * d x y`, and a number whose double is non-negative is non-negative.

The argument is worth a second look, because it is the standard use of the triangle inequality: take the detour that returns to where it started, and read the inequality backwards.
@description
Show that `0 ≤ M.dist x y`. Begin with `M.triangle x y x`, rewrite the distance from `x` to itself with the previous problem and the distance from `y` to `x` with symmetry, and let `linarith` do the arithmetic.
-/
theorem Metric.nonneg {X : Type u} (M : Metric X) (x y : X) : 0 ≤ M.dist x y := by
  have h := M.triangle x y x
  rw [M.dist_self x, M.symm y x] at h
  linarith

/-!
@concept real_line
@title The Real Line as a Metric Space
@kind definition

A definition with no examples under it is an empty one. The first example is the line itself: the real numbers, where the distance between two of them is the size of their difference. Every one of the three conditions is then a standard fact about the absolute value, and the whole of this section can be read with the line in mind.
-/

/-!
@problem define_line
@title The Metric on the Real Line
@concept real_line

@preamble
How far apart are two real numbers? By `|x - y|`, the absolute value of their difference, which is `x - y` when that is non-negative and `y - x` when it is not. The three conditions hold, and each is a fact about the absolute value that Mathlib already knows. Symmetry is `abs_sub_comm`, which says `|a - b| = |b - a|`. The triangle inequality is `abs_sub_le`, which says `|a - c| ≤ |a - b| + |b - c|` and is where the inequality got its name. Non-degeneracy needs two steps: `abs_eq_zero` says `|a| = 0 ↔ a = 0`, and `sub_eq_zero` says `a - b = 0 ↔ a = b`.

To give a term of a structure type is to give each of its fields, and Lean writes this with `where` and one line per field:
```lean
def someMetric : Metric ℝ where
  dist x y := ...
  symm x y := ...
  triangle x y z := ...
  eq_zero x y := ...
```
The first line is a definition; the other three are proofs, and a proof may be written as a term or opened with `by`.
@description
Define `line`, the real numbers with `dist x y = |x - y|`. Three of the fields are the Mathlib facts named above applied to the right arguments; for the fourth, rewriting with `abs_eq_zero` and then `sub_eq_zero` turns the goal into one that `rw` closes by itself.
-/

def line : Metric ℝ where
  dist x y := |x - y|
  symm x y := abs_sub_comm x y
  triangle x y z := abs_sub_le x y z
  eq_zero x y := by rw [abs_eq_zero, sub_eq_zero]

/-- @spec -/
example (x y : ℝ) : line.dist x y = |x - y| := rfl

/-! @end -/

/-!
@concept open_ball
@title Open Balls, Closed Balls and Spheres
@kind definition

Around each point of a metric space, and for each radius, lies the set of points nearer to it than that radius: an open ball. Balls are how a metric is used. Almost every notion built on a metric — bounded, open, convergent, continuous — is stated by saying that some ball is contained in something, and the distances themselves appear only inside the definition of the ball.
-/

/-!
@problem define_ball
@title The Open Ball
@concept open_ball

@preamble
Fix a point `x` of a metric space and a real number `ε`. The *open ball* of radius `ε` about `x` is the set of points whose distance from `x` is less than `ε`. On paper it is written `B(x, ε)`; here it is `M.ball x ε`, since the metric must be named as well. It is called open because the inequality is strict: the points at distance exactly `ε` are left out.

The radius is any real number, not only a positive one. A ball of radius zero or of negative radius is empty, since no distance is negative, and it costs nothing to allow it.

Sets in this subject are Mathlib's. A set of elements of a type `X` is a term of type `Set X`, and `{y | p y}` denotes the set of those `y` for which `p y` holds. Membership `y ∈ {z | p z}` is by definition the proposition `p y`, so a statement about membership in a ball is a statement about a distance, written differently.
@description
Define `Metric.ball`, and then prove `Metric.mem_ball`, which says that `y` lies in `M.ball x ε` exactly when `M.dist x y < ε`. The two sides of that equivalence are the same proposition by definition, so `Iff.rfl` proves it.
-/

def Metric.ball {X : Type u} (M : Metric X) (x : X) (ε : ℝ) : Set X :=
  {y | M.dist x y < ε}

theorem Metric.mem_ball {X : Type u} (M : Metric X) (x y : X) (ε : ℝ) :
    y ∈ M.ball x ε ↔ M.dist x y < ε := Iff.rfl

/-! @end -/

/--
@problem mem_ball_self
@title A Ball Contains Its Own Centre
@concept open_ball

@preamble
A ball of positive radius contains the point it is drawn about, because the distance from that point to itself is zero and zero is less than the radius. The hypothesis that the radius is positive cannot be dropped: a ball of radius zero contains nothing at all, its own centre included.

This small fact is used constantly. A ball is a way of saying "near `x`", and it would be a poor one if `x` itself were not near `x`.
@description
Show that `x ∈ M.ball x ε` whenever `0 < ε`. Rewriting with `M.mem_ball` turns the membership into an inequality between distances, and rewriting that with `M.dist_self` leaves the hypothesis.
-/
theorem Metric.mem_ball_self {X : Type u} (M : Metric X) (x : X) (ε : ℝ) (h : 0 < ε) :
    x ∈ M.ball x ε := by
  rw [M.mem_ball, M.dist_self]
  exact h

/-!
@problem define_closed_ball
@title The Closed Ball and the Sphere
@concept open_ball

@preamble
The open ball has two companions, got by changing the inequality. The *closed ball* of radius `ε` about `x` admits the points at distance exactly `ε` as well, and the *sphere* of radius `ε` about `x` is made of those points alone: the boundary the open ball stops short of.

In the plane with its ordinary distance the three are the disc without its edge, the disc with its edge, and the circle, which is where the names come from. On the real line they are an open interval, the corresponding closed interval, and the pair of its endpoints. In a space of one point they are stranger, and in general a sphere may be empty.

Since the strict inequality implies the weak one, the open ball is contained in the closed ball of the same radius.
@description
Define `Metric.closedBall` and `Metric.sphere`, and then show that `M.ball x ε ⊆ M.closedBall x ε`. A containment is proved by introducing a point and a proof that it lies in the first set; `have h : M.dist x y < ε := hy` restates that proof as the inequality it already is, `show` does the same for the goal, and `linarith` closes the gap between `<` and `≤`.
-/

def Metric.closedBall {X : Type u} (M : Metric X) (x : X) (ε : ℝ) : Set X :=
  {y | M.dist x y ≤ ε}

def Metric.sphere {X : Type u} (M : Metric X) (x : X) (ε : ℝ) : Set X :=
  {y | M.dist x y = ε}

theorem Metric.ball_subset_closedBall {X : Type u} (M : Metric X) (x : X) (ε : ℝ) :
    M.ball x ε ⊆ M.closedBall x ε := by
  intro y hy
  have h : M.dist x y < ε := hy
  show M.dist x y ≤ ε
  linarith

/-- @spec -/
example (X : Type) (M : Metric X) (x y : X) (ε : ℝ) :
    (y ∈ M.closedBall x ε ↔ M.dist x y ≤ ε) ∧ (y ∈ M.sphere x ε ↔ M.dist x y = ε) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! @end -/

/--
@problem ball_mono
@title Balls Grow With Their Radius
@concept open_ball

@preamble
Two balls about the same centre are nested, the one of smaller radius inside the one of larger: a point nearer to `x` than `ε` is nearer to `x` than any `δ` at least as large. So the balls about a fixed point form a family increasing with the radius, and to say that something holds "for all small enough radii" is to say that it holds for one.
@description
Show that `M.ball x ε ⊆ M.ball x δ` when `ε ≤ δ`. A containment is a function taking a point and a proof of membership to a proof of membership, so the whole proof can be written as `fun _ hy => ...`; `lt_of_lt_of_le` chains a strict inequality with a weak one.
-/
theorem Metric.ball_mono {X : Type u} (M : Metric X) (x : X) {ε δ : ℝ} (h : ε ≤ δ) :
    M.ball x ε ⊆ M.ball x δ :=
  fun _ hy => lt_of_lt_of_le hy h

/--
@problem line_ball
@title Balls on the Real Line Are Intervals
@concept open_ball

@preamble
On the real line a ball is an interval, and this is the picture to keep. The numbers `y` with `|x - y| < ε` are those that differ from `x` by less than `ε` in either direction, that is, those with `x - ε < y` and `y < x + ε`. The ball of radius `ε` about `x` is the interval of width `2 * ε` centred at `x`.

The fact that turns an absolute value into a pair of inequalities is `abs_lt`, which says that `|a| < b` holds exactly when `-b < a` and `a < b`.
@description
Show that `line.ball x ε` is the set `{y | x - ε < y ∧ y < x + ε}`. Two sets are equal when they have the same elements, which is what `ext y` asks you to prove; `show` restates the membership on the left as the inequality `|x - y| < ε` that it abbreviates, `Set.mem_setOf_eq` does the same on the right, `abs_lt` splits the absolute value, and `linarith` rearranges each of the four resulting inequalities.
-/
theorem line_ball (x ε : ℝ) : line.ball x ε = {y | x - ε < y ∧ y < x + ε} := by
  ext y
  show |x - y| < ε ↔ _
  rw [Set.mem_setOf_eq, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/--
@problem ball_subset_ball
@title A Ball Inside a Ball About Another Centre
@concept open_ball

@preamble
Here is the triangle inequality translated into the language of balls, which is the form in which it is almost always used.

Let `x` and `y` be two points, at distance `M.dist x y` from one another. A point `z` within `ε` of `y` is then within `M.dist x y + ε` of `x`, since the journey from `x` to `z` may be made through `y`. So a ball about `y` sits inside a ball about `x`, and the price of moving the centre is exactly the distance the centre moved.

One consequence is that the centre of a ball hardly matters. Any ball, about any point, is contained in some ball about any other point; only the radius has to grow.
@description
Show that `M.ball y ε ⊆ M.ball x (M.dist x y + ε)`. Introduce a point `z` and its membership, rewrite both that hypothesis and the goal with `M.mem_ball`, and give `linarith` the instance `M.triangle x y z` of the triangle inequality.
-/
theorem Metric.ball_subset_ball {X : Type u} (M : Metric X) (x y : X) (ε : ℝ) :
    M.ball y ε ⊆ M.ball x (M.dist x y + ε) := by
  intro z hz
  rw [M.mem_ball] at hz ⊢
  have h := M.triangle x y z
  linarith

/-!
@concept bounded_set
@title Bounded Subsets
@kind definition

A subset of a metric space is bounded when it does not run away to infinity — when one ball, of some finite radius, already holds the whole of it. The notion belongs to the metric and not to the space underneath: the same set may be bounded for one distance and unbounded for another, as the plane will show.
-/

/-!
@problem define_is_bounded
@title The Definition of a Bounded Set
@concept bounded_set

@preamble
A subset `S` of a metric space is *bounded* if some ball contains it: if there are a point `x` and a radius `ε` with `S ⊆ M.ball x ε`. Which point is chosen does not matter, by the last problem of the previous concept — a ball about one point lies inside a ball about any other, at the cost of a larger radius — so the content of the definition is that some finite radius suffices at all.

The statement "there are an `x` and an `ε` such that …" is written in Lean with nested existential quantifiers, and a proof of it is the two witnesses together with a proof of the remaining claim, written `⟨x, ε, h⟩`.
@description
Define `Metric.IsBounded`, and then show that a ball is a bounded set. For the second, the ball is contained in itself, which is `subset_rfl`.
-/

def Metric.IsBounded {X : Type u} (M : Metric X) (S : Set X) : Prop :=
  ∃ (x : X) (ε : ℝ), S ⊆ M.ball x ε

theorem Metric.isBounded_ball {X : Type u} (M : Metric X) (x : X) (ε : ℝ) :
    M.IsBounded (M.ball x ε) :=
  ⟨x, ε, subset_rfl⟩

/-- @spec -/
example (X : Type) (M : Metric X) (S : Set X) :
    M.IsBounded S ↔ ∃ (x : X) (ε : ℝ), S ⊆ M.ball x ε := Iff.rfl

/-! @end -/

/--
@problem is_bounded_subset
@title A Subset of a Bounded Set is Bounded
@concept bounded_set

@preamble
Anything inside something bounded is bounded, and by the same ball: if `T ⊆ S` and `S` lies in a ball, then `T` lies in that ball. The proof is the composition of two containments, and no property of the metric is used at all.
@description
Show that `M.IsBounded T` follows from `M.IsBounded S` and `T ⊆ S`. `obtain ⟨x, ε, hx⟩ := h` takes the hypothesis apart into the centre, the radius and the containment, and the same centre and radius will do.
-/
theorem Metric.isBounded_subset {X : Type u} (M : Metric X) (S T : Set X)
    (h : M.IsBounded S) (hTS : T ⊆ S) : M.IsBounded T := by
  obtain ⟨x, ε, hx⟩ := h
  exact ⟨x, ε, fun y hy => hx (hTS hy)⟩

/--
@problem is_bounded_union
@title The Union of Two Bounded Sets is Bounded
@concept bounded_set

@preamble
Two bounded sets need not be held by the same ball, but a single ball can be made to hold both. Suppose `S` lies in the ball of radius `ε` about `x`, and `T` in the ball of radius `δ` about `y`. Moving the second centre to the first costs the distance between them, so `T` lies in the ball about `x` of radius `M.dist x y + δ`. Take whichever of the two radii is larger and the ball about `x` of that radius contains both.

The restriction to two sets is essential, and the proof shows why: among finitely many radii there is a largest, and among infinitely many there need not be. The union of all the balls about a fixed point is usually the whole space, bounded or not.
@description
Show that `M.IsBounded (S ∪ T)`. Take both hypotheses apart, offer `x` as the centre and `max ε (M.dist x y + δ)` as the radius, and use `rintro z (hz | hz)` to split on which of the two sets a point of the union came from. `Metric.ball_mono` with `le_max_left` handles the first case, and the same with `le_max_right` handles the second once `Metric.ball_subset_ball` has moved the centre.
-/
theorem Metric.isBounded_union {X : Type u} (M : Metric X) (S T : Set X)
    (hS : M.IsBounded S) (hT : M.IsBounded T) : M.IsBounded (S ∪ T) := by
  obtain ⟨x, ε, hx⟩ := hS
  obtain ⟨y, δ, hy⟩ := hT
  refine ⟨x, max ε (M.dist x y + δ), ?_⟩
  rintro z (hz | hz)
  · exact M.ball_mono x (le_max_left _ _) (hx hz)
  · exact M.ball_mono x (le_max_right _ _) (M.ball_subset_ball x y δ (hy hz))

/-!
@concept normed_space
@title Normed Vector Spaces
@kind definition

Most metrics are not given directly. They come from a length: in a space where vectors can be added and scaled, one measures the size of a single vector, and the distance between two vectors is then the size of their difference. A rule that measures the size of a vector is a norm, and this concept is about the conditions it must satisfy.
-/

/-!
@problem define_norm
@title The Definition of a Norm
@concept normed_space

@preamble
A real vector space is a set whose elements can be added to one another and scaled by real numbers. A *norm* on it assigns to each vector `v` a real number, its length, subject to three conditions.

*Non-degeneracy*: the length of `v` is zero exactly when `v` is the zero vector. Only the origin has no size.

*Homogeneity*: scaling a vector by a real number `c` scales its length by `|c|`, so that `‖c • v‖ = |c| * ‖v‖`. The absolute value is there because scaling by a negative number turns a vector around without making it any shorter.

*The triangle inequality*: `‖v + w‖ ≤ ‖v‖ + ‖w‖`. Two displacements made one after the other carry one no further than the sum of their lengths.

In Lean a type `V` is a real vector space when it carries the two instances `[AddCommGroup V]`, which provides `+`, `-`, `0` and negation, and `[Module ℝ V]`, which provides the scaling, written `c • v`. Both appear in the signature of the structure, before the fields.
@description
Define the structure `Norm V` for a real vector space `V`, with four fields in this order: `norm`, of type `V → ℝ`; then `eq_zero`, `smul` and `triangle`, carrying the equivalence `norm v = 0 ↔ v = 0`, the equation `norm (c • v) = |c| * norm v` for every real `c`, and the inequality `norm (v + w) ≤ norm v + norm w`, each quantified over the vectors it mentions.
-/

structure Norm (V : Type u) [AddCommGroup V] [Module ℝ V] where
  norm : V → ℝ
  eq_zero : ∀ v, norm v = 0 ↔ v = 0
  smul : ∀ (c : ℝ) (v : V), norm (c • v) = |c| * norm v
  triangle : ∀ v w, norm (v + w) ≤ norm v + norm w

/-- @spec -/
example (V : Type) [AddCommGroup V] [Module ℝ V] (N : Norm V) (c : ℝ) (v w : V) :
    (N.norm v = 0 ↔ v = 0)
      ∧ N.norm (c • v) = |c| * N.norm v
      ∧ N.norm (v + w) ≤ N.norm v + N.norm w :=
  ⟨N.eq_zero v, N.smul c v, N.triangle v w⟩

/-! @end -/

/-!
@problem norm_zero_and_neg
@title The Length of Zero and of a Negative
@concept normed_space

@preamble
Two consequences of the conditions, both needed below.

The zero vector has length zero. This is the right-to-left direction of non-degeneracy, applied to `0`.

A vector and its negative have the same length. The reason is homogeneity: `-v` is `(-1) • v`, so its length is `|-1|` times the length of `v`, and `|-1|` is `1`. Geometrically, turning a vector around does not change how long it is.
@description
Prove both. For the first, apply the right-to-left direction of `N.eq_zero` at `0`. For the second, start from the instance `N.smul (-1) v` of homogeneity, rewrite `(-1) • v` as `-v` with `neg_one_smul`, and then clear the factor with `abs_neg`, `abs_one` and `one_mul`.
-/

theorem Norm.zero {V : Type u} [AddCommGroup V] [Module ℝ V] (N : Norm V) : N.norm 0 = 0 :=
  (N.eq_zero 0).mpr rfl

theorem Norm.neg {V : Type u} [AddCommGroup V] [Module ℝ V] (N : Norm V) (v : V) :
    N.norm (-v) = N.norm v := by
  have h := N.smul (-1) v
  rw [neg_one_smul] at h
  rw [h, abs_neg, abs_one, one_mul]

/-! @end -/

/--
@problem norm_nonneg
@title Lengths Are Never Negative
@concept normed_space

@preamble
As with a distance, non-negativity was not asked for and does not have to be. The vector `v + (-v)` is the zero vector, whose length is zero; the triangle inequality bounds that zero by `‖v‖ + ‖-v‖`, which is twice `‖v‖` since a vector and its negative have the same length. A number whose double is non-negative is non-negative.

This is the same argument as the one for distances, with the detour that returns to its starting point replaced by a vector added to its own negative.
@description
Show that `0 ≤ N.norm v`. Begin with `N.triangle v (-v)`, rewrite it with `add_neg_cancel`, `N.zero` and `N.neg`, and finish with `linarith`.
-/
theorem Norm.nonneg {V : Type u} [AddCommGroup V] [Module ℝ V] (N : Norm V) (v : V) :
    0 ≤ N.norm v := by
  have h := N.triangle v (-v)
  rw [add_neg_cancel, N.zero, N.neg] at h
  linarith

/-!
@concept norm_metric
@title The Metric of a Norm
@kind theorem

A norm measures one vector; the distance between two is the length of their difference. This turns every normed vector space into a metric space, and it is where almost all the metrics of analysis come from. The construction is the content of this concept, and the real line, measured by the absolute value, is its first instance.
-/

/--
@problem norm_sub_comm
@title The Length of a Difference Does Not Depend on the Order
@concept norm_metric

@preamble
The differences `v - w` and `w - v` are negatives of one another, and a vector and its negative have the same length. So the length of a difference does not depend on the order in which the two vectors are written — which is exactly the symmetry that the distance defined from a norm will need.
@description
Show that `N.norm (v - w) = N.norm (w - v)`. Rewriting the goal backwards with `N.neg (v - w)` puts a negation in its way, and `neg_sub` turns `-(v - w)` into `w - v`.
-/
theorem Norm.sub_comm {V : Type u} [AddCommGroup V] [Module ℝ V] (N : Norm V) (v w : V) :
    N.norm (v - w) = N.norm (w - v) := by
  rw [← N.neg (v - w), neg_sub]

/-!
@problem norm_to_metric
@title Every Norm Induces a Metric
@concept norm_metric

@preamble
Define the distance between two vectors to be the length of their difference: `d v w = ‖v - w‖`. The three conditions on a metric then follow from the three conditions on a norm.

Symmetry is the problem above. Non-degeneracy holds because `‖v - w‖` is zero exactly when `v - w` is the zero vector, and a difference is zero exactly when the two vectors agree. The triangle inequality is the norm's, applied to the pair of vectors `u - v` and `v - w`, whose sum is `u - w`; the detour through `v` in the metric is the splitting of a displacement into two in the vector space.

Note which of the norm's conditions is not used: homogeneity plays no part here. It is what distinguishes the metrics that come from norms from metrics in general, and a metric space need not have any vector space under it at all.
@description
Define `Norm.toMetric`, the metric induced by a norm. For the triangle inequality, apply `N.triangle` to `u - v` and `v - w` and rewrite the result with `sub_add_sub_cancel`; for non-degeneracy, rewrite with `N.eq_zero` and then `sub_eq_zero`.
-/

def Norm.toMetric {V : Type u} [AddCommGroup V] [Module ℝ V] (N : Norm V) : Metric V where
  dist v w := N.norm (v - w)
  symm v w := N.sub_comm v w
  triangle u v w := by
    have h := N.triangle (u - v) (v - w)
    rw [sub_add_sub_cancel] at h
    exact h
  eq_zero v w := by rw [N.eq_zero, sub_eq_zero]

/-- @spec -/
example (V : Type) [AddCommGroup V] [Module ℝ V] (N : Norm V) (v w : V) :
    N.toMetric.dist v w = N.norm (v - w) := rfl

/-! @end -/

/--
@problem mem_ball_zero
@title The Ball About the Origin
@concept norm_metric

@preamble
In a normed space the ball about the origin is the set of vectors shorter than its radius. The distance from `0` to `v` is `‖0 - v‖`, which is `‖-v‖`, which is `‖v‖`.

This is the ball one draws when asking what a norm looks like, and every other ball is a translate of it. The two norms of the next concept are told apart precisely by the shape of this one set.
@description
Show that `v ∈ N.toMetric.ball 0 ε` exactly when `N.norm v < ε`. Rewrite with `Metric.mem_ball`, use `show` to restate the distance as the length it is, and rewrite that with `zero_sub` and `N.neg`.
-/
theorem Norm.mem_ball_zero {V : Type u} [AddCommGroup V] [Module ℝ V] (N : Norm V)
    (v : V) (ε : ℝ) : v ∈ N.toMetric.ball 0 ε ↔ N.norm v < ε := by
  rw [Metric.mem_ball]
  show N.norm (0 - v) < ε ↔ N.norm v < ε
  rw [zero_sub, N.neg]

/-!
@problem define_abs_norm
@title The Absolute Value as a Norm
@concept norm_metric

@preamble
The real numbers are themselves a real vector space, of dimension one, and the length of a number is its absolute value. The three conditions are again standard facts: `abs_eq_zero` for non-degeneracy, `abs_mul` for homogeneity once `smul_eq_mul` has said that scaling a real number is multiplying it, and `abs_add_le` for the triangle inequality.

This is the Euclidean length in dimension one. The Euclidean length of a vector with coordinates `x₁, …, xₙ` is the square root of `x₁² + ⋯ + xₙ²`, and for a single coordinate that is the square root of `x²`, which is `|x|`. In higher dimensions the square root is unavoidable, and square roots are beyond what this section is built from; the next concept measures the plane with two lengths that need no roots at all.

The construction of the previous problem should now return the metric we began with. It does, and on the nose: the distance it produces is `|x - y|`, which is what `line` was defined to be, so the two metrics are not merely equal but identical as they stand.
@description
Define `absNorm`, the absolute value as a norm on `ℝ`, and then show that the metric it induces is the `line` defined at the start of the section. The three fields are the facts named above, the second after rewriting with `smul_eq_mul` and `abs_mul`; and the two metrics are the same by `rfl`.
-/

def absNorm : Norm ℝ where
  norm x := |x|
  eq_zero x := abs_eq_zero
  smul c x := by rw [smul_eq_mul, abs_mul]
  triangle x y := abs_add_le x y

theorem absNorm_toMetric : absNorm.toMetric = line := rfl

/-- @spec -/
example (x : ℝ) : absNorm.norm x = |x| := rfl

/-! @end -/

/-!
@concept plane_norms
@title Two Norms on the Plane
@kind definition
@goal

On the line there was only one reasonable length. On the plane there are many, and two of them can be written down without a square root: the sum of the magnitudes of the two coordinates, and the larger of them. Their unit balls are a diamond and a square, so the two lengths are certainly not the same function. Yet inside every ball of either one there is a ball of the other about the same point, and a notion defined by "some ball about `x` lies inside `S`" therefore cannot tell them apart. That is where topology begins.
-/

/--
@problem eq_zero_of_abs_le_zero
@title A Number Whose Magnitude is at Most Zero
@concept plane_norms

@preamble
Both of the norms below vanish only at the zero vector, and in both cases the argument passes through the same small fact: an absolute value is never negative, so one that is at most zero is exactly zero, and a number whose absolute value is zero is zero. Since it is wanted twice, we prove it once.

Proving a small thing separately is not only economy. The two proofs below would each be a dozen lines with this argument inlined, and a dozen-line proof is one nobody reads.
@description
Show that `a = 0` follows from `|a| ≤ 0`. Rewriting the goal backwards with `abs_eq_zero` asks instead for `|a| = 0`, and `abs_nonneg a` together with the hypothesis gives that to `linarith`.
-/
theorem eq_zero_of_abs_le_zero {a : ℝ} (h : |a| ≤ 0) : a = 0 := by
  rw [← abs_eq_zero]
  have h0 := abs_nonneg a
  linarith

/--
@problem abs_add_abs_eq_zero
@title When a Sum of Magnitudes Vanishes
@concept plane_norms

@preamble
Two non-negative numbers add up to zero only if both are zero, since neither can be made up for by the other. So `|a| + |b| = 0` holds exactly when `a` and `b` are both zero. This is the non-degeneracy of the first norm on the plane, written out in coordinates before the norm itself is defined.
@description
Show that `|a| + |b| = 0` exactly when `a = 0` and `b = 0`. In one direction, `abs_nonneg` applied to each of `a` and `b` puts each magnitude within reach of the previous problem; in the other, rewrite by the two hypotheses and clear the result with `abs_zero` and `add_zero`.
-/
theorem abs_add_abs_eq_zero {a b : ℝ} : |a| + |b| = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    exact ⟨eq_zero_of_abs_le_zero (by linarith), eq_zero_of_abs_le_zero (by linarith)⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb, abs_zero, add_zero]

/--
@problem prod_eq_zero
@title The Zero Vector of the Plane
@concept plane_norms

@preamble
The zero vector of the plane is the pair whose coordinates are both zero, and a pair is the zero vector exactly when each of its coordinates is zero. This deserves recording on its own because both of the norms below need it, and both need it in the same place: non-degeneracy is a statement about a vector, while a norm on the plane is written in coordinates, and something has to carry one over to the other.

Two pairs are equal when their coordinates are equal, which is `Prod.ext`. In the other direction the coordinates of the zero vector are zero by definition, so each half is `rfl`.
@description
Show that a point `v` of the plane is the zero vector exactly when `v.1 = 0` and `v.2 = 0`. One direction rewrites by the hypothesis and then offers `rfl` for each coordinate; the other is `Prod.ext`.
-/
theorem prod_eq_zero {v : ℝ × ℝ} : v = 0 ↔ v.1 = 0 ∧ v.2 = 0 := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2

/-!
@problem define_taxicab
@title The Taxicab Norm
@concept plane_norms

@preamble
The first length on the plane adds the magnitudes of the two coordinates: the length of `(x, y)` is `|x| + |y|`. It is the distance a taxicab drives in a city laid out on a square grid, where one may travel east and north but not diagonally, and it is called the taxicab norm for that reason. Its unit ball, the vectors of length less than one, is the diamond with corners at `(1, 0)`, `(0, 1)`, `(-1, 0)` and `(0, -1)`.

A point of the plane is a pair, a term `v : ℝ × ℝ` with coordinates `v.1` and `v.2`. Addition and scaling act on each coordinate separately, so `(v + w).1` is `v.1 + w.1` and `(c • v).1` is `c * v.1`, each by definition. Two pairs are equal when their coordinates are, which is `Prod.ext`.

Each of the three conditions comes down to the corresponding fact about absolute values, one coordinate at a time.
@description
Define `taxicab`, the norm on `ℝ × ℝ` sending `v` to `|v.1| + |v.2|`. Non-degeneracy is the two previous problems, one after the other, rewritten into the goal; for the other two conditions, `show` the goal in coordinates first, then `abs_mul` on each coordinate with `ring`, and `abs_add_le` on each coordinate with `linarith`.
-/

def taxicab : Norm (ℝ × ℝ) where
  norm v := |v.1| + |v.2|
  eq_zero v := by rw [abs_add_abs_eq_zero, prod_eq_zero]
  smul c v := by
    show |c * v.1| + |c * v.2| = |c| * (|v.1| + |v.2|)
    rw [abs_mul, abs_mul]
    ring
  triangle v w := by
    show |v.1 + w.1| + |v.2 + w.2| ≤ |v.1| + |v.2| + (|w.1| + |w.2|)
    have h1 := abs_add_le v.1 w.1
    have h2 := abs_add_le v.2 w.2
    linarith

/-- @spec -/
example (v : ℝ × ℝ) : taxicab.norm v = |v.1| + |v.2| := rfl

/-! @end -/

/--
@problem max_abs_eq_zero
@title When a Larger of Two Magnitudes Vanishes
@concept plane_norms

@preamble
The same question for the second norm. The larger of two non-negative numbers is zero exactly when both are, since each of them is at most the larger. The fact that bounds a number by a maximum is `le_max_left`, with `le_max_right` for the other side.
@description
Show that `max |a| |b| = 0` exactly when `a = 0` and `b = 0`. In one direction, rewrite the hypothesis into the bounds that `le_max_left` and `le_max_right` provide and hand each result to `eq_zero_of_abs_le_zero`; in the other, rewrite by the two hypotheses and close with `abs_zero` and `max_self`.
-/
theorem max_abs_eq_zero {a b : ℝ} : max |a| |b| = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha := le_max_left |a| |b|
    have hb := le_max_right |a| |b|
    rw [h] at ha hb
    exact ⟨eq_zero_of_abs_le_zero ha, eq_zero_of_abs_le_zero hb⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb, abs_zero, max_self]

/--
@problem max_add_max
@title A Maximum of Sums
@concept plane_norms

@preamble
The maximum of two sums is at most the sum of the two maxima: `max (a + c) (b + d) ≤ max a b + max c d`. Each of the two sums is bounded by the right-hand side one summand at a time, since `a` and `b` are both at most `max a b` and `c` and `d` are both at most `max c d`; and a bound holding for both of two numbers holds for their maximum.

This is the triangle inequality of the next problem with the absolute values stripped away. Proved separately it keeps that proof to a few lines, and it is the shape of the argument rather than anything about lengths that is doing the work.
@description
Show that `max (a + c) (b + d) ≤ max a b + max c d`. `max_le_iff` turns the goal into a pair of bounds, `le_max_left` and `le_max_right` supply the four facts they need, and `linarith` closes both.
-/
theorem max_add_max (a b c d : ℝ) : max (a + c) (b + d) ≤ max a b + max c d := by
  rw [max_le_iff]
  have a1 := le_max_left a b
  have a2 := le_max_right a b
  have b1 := le_max_left c d
  have b2 := le_max_right c d
  constructor <;> linarith

/-!
@problem define_sup_norm
@title The Supremum Norm
@concept plane_norms

@preamble
The second length on the plane keeps only the larger of the two magnitudes: the length of `(x, y)` is `max |x| |y|`. Its unit ball is the square with corners at `(1, 1)`, `(1, -1)`, `(-1, -1)` and `(-1, 1)` — the vectors both of whose coordinates are smaller than one in magnitude.

The two norms are the ends of a family. For each `p` at least one there is a length `(|x|^p + |y|^p)^(1/p)`, which at `p = 1` is the taxicab norm and at `p = 2` the Euclidean one. As `p` grows the `p`-th root suppresses the smaller coordinate more and more, and in the limit only the larger survives; hence the name supremum norm, and the traditional index `∞`. The two members we can write down without a root are the two ends, `p = 1` and `p = ∞`.

Homogeneity needs one fact beyond the previous norm: a non-negative factor may be moved through a maximum, which is `mul_max_of_nonneg`. For the triangle inequality, bound each coordinate of `v + w` by the corresponding sum of magnitudes, which `max_le_max` carries through the maximum, and then apply the problem above.
@description
Define `supNorm`, the norm on `ℝ × ℝ` sending `v` to `max |v.1| |v.2|`. Non-degeneracy is `max_abs_eq_zero` and then `prod_eq_zero`, as for the taxicab norm; homogeneity follows from `abs_mul` on each coordinate and `mul_max_of_nonneg`; and for the triangle inequality, feed `max_le_max` the two coordinatewise instances of `abs_add_le` and hand the result, together with `max_add_max`, to `linarith`.
-/

def supNorm : Norm (ℝ × ℝ) where
  norm v := max |v.1| |v.2|
  eq_zero v := by rw [max_abs_eq_zero, prod_eq_zero]
  smul c v := by
    show max |c * v.1| |c * v.2| = |c| * max |v.1| |v.2|
    rw [abs_mul, abs_mul, mul_max_of_nonneg _ _ (abs_nonneg c)]
  triangle v w := by
    show max |v.1 + w.1| |v.2 + w.2| ≤ max |v.1| |v.2| + max |w.1| |w.2|
    have h1 := max_le_max (abs_add_le v.1 w.1) (abs_add_le v.2 w.2)
    have h2 := max_add_max |v.1| |v.2| |w.1| |w.2|
    linarith

/-- @spec -/
example (v : ℝ × ℝ) : supNorm.norm v = max |v.1| |v.2| := rfl

/-! @end -/

/--
@problem sup_norm_le_taxicab
@title The Supremum Norm is at Most the Taxicab Norm
@concept plane_norms

@preamble
The larger of two non-negative numbers is at most their sum, since the other one is not negative. So every vector is at most as long in the supremum norm as in the taxicab norm. On the picture, the diamond lies inside the square.
@description
Show that `supNorm.norm v ≤ taxicab.norm v`. Use `show` to put the goal in coordinates, `max_le_iff` to reduce a bound on a maximum to two bounds, and `abs_nonneg` on each coordinate so that `linarith` can close both.
-/
theorem supNorm_le_taxicab (v : ℝ × ℝ) : supNorm.norm v ≤ taxicab.norm v := by
  show max |v.1| |v.2| ≤ |v.1| + |v.2|
  have h1 := abs_nonneg v.1
  have h2 := abs_nonneg v.2
  rw [max_le_iff]
  constructor <;> linarith

/--
@problem taxicab_le_two_sup_norm
@title The Taxicab Norm is at Most Twice the Supremum Norm
@concept plane_norms

@preamble
In the other direction the two norms differ by a factor of at most two, and no better constant will do: at `(1, 1)` the taxicab length is `2` and the supremum length is `1`. Each magnitude is at most the maximum, so their sum is at most twice it.

A pair of inequalities of this shape, each norm bounded by a constant multiple of the other, is what it means for two norms to be equivalent. The last two problems of this section draw the consequence.
@description
Show that `taxicab.norm v ≤ 2 * supNorm.norm v`. Each coordinate's magnitude is bounded by the maximum, which is what `le_max_left` and `le_max_right` say.
-/
theorem taxicab_le_two_supNorm (v : ℝ × ℝ) : taxicab.norm v ≤ 2 * supNorm.norm v := by
  show |v.1| + |v.2| ≤ 2 * max |v.1| |v.2|
  have h1 := le_max_left |v.1| |v.2|
  have h2 := le_max_right |v.1| |v.2|
  linarith

/--
@problem unit_balls_differ
@title The Two Unit Balls Are Different Sets
@concept plane_norms

@preamble
The two norms are genuinely different functions, and one point is enough to show it. Take `(3/4, 3/4)`. The larger of the magnitudes of its coordinates is `3/4`, which is less than one, so the point lies in the unit ball of the supremum norm. Their sum is `3/2`, which is not less than one, so it does not lie in the unit ball of the taxicab norm. The two balls are therefore not the same set.

On the picture this is the corner of the square poking out beyond the diamond. Any point of the square near one of its corners will do, and the diamond has no points at all beyond the square, since the taxicab length is the larger of the two.
@description
Show that the two unit balls about the origin are different sets. Assume they are equal, put `(3/4, 3/4)` into the first with `supNorm.mem_ball_zero`, carry it across the assumed equality with `rw`, and contradict it with the same computation for the taxicab norm. In each computation `show` puts the goal in coordinates and `abs_of_nonneg` removes the absolute values, after which `norm_num` settles the arithmetic.
-/
theorem unit_balls_differ :
    supNorm.toMetric.ball (0 : ℝ × ℝ) 1 ≠ taxicab.toMetric.ball (0 : ℝ × ℝ) 1 := by
  intro h
  have hin : ((3/4, 3/4) : ℝ × ℝ) ∈ supNorm.toMetric.ball (0 : ℝ × ℝ) 1 := by
    rw [supNorm.mem_ball_zero]
    show max |(3/4 : ℝ)| |(3/4 : ℝ)| < 1
    rw [max_self, abs_of_nonneg] <;> norm_num
  rw [h, taxicab.mem_ball_zero] at hin
  have hout : ¬ (taxicab.norm ((3/4, 3/4) : ℝ × ℝ) < 1) := by
    show ¬ (|(3/4 : ℝ)| + |(3/4 : ℝ)| < 1)
    rw [abs_of_nonneg] <;> norm_num
  exact hout hin

/-!
@problem equivalent_norms
@title Each Norm's Balls Fit Inside the Other's
@concept plane_norms

@preamble
Different as the two unit balls are, neither norm sees anything the other misses.

Since the supremum norm is at most the taxicab norm, a vector short in the taxicab norm is short in the supremum norm, and every taxicab ball lies inside the supremum ball of the same radius about the same point. Since the taxicab norm is at most twice the supremum norm, the supremum ball of half a radius lies inside the taxicab ball of that radius. Put together: inside any ball of one norm there is a ball of the other about the same centre.

Two metrics standing in this relation are called *equivalent*. They assign different numbers to the same pair of points, and their balls are different sets, but a statement of the form "some ball about `x` is contained in `S`" holds for one exactly when it holds for the other. Every notion in the rest of this subject — open, closed, convergent, continuous, compact — is of that form. None of them can distinguish these two metrics, and what is left when the distances have been forgotten and only such statements remain is the topology.
@description
Prove the two containments. In each, introduce a point and its membership; `have h : ... := hy` restates that membership as the inequality between lengths it abbreviates, `show` does the same for the goal, and the comparison proved in one of the previous two problems, applied to `x - y`, lets `linarith` finish.
-/

theorem ball_taxicab_subset_supNorm (x : ℝ × ℝ) (ε : ℝ) :
    taxicab.toMetric.ball x ε ⊆ supNorm.toMetric.ball x ε := by
  intro y hy
  have h : taxicab.norm (x - y) < ε := hy
  have h2 := supNorm_le_taxicab (x - y)
  show supNorm.norm (x - y) < ε
  linarith

theorem ball_supNorm_subset_taxicab (x : ℝ × ℝ) (ε : ℝ) :
    supNorm.toMetric.ball x (ε / 2) ⊆ taxicab.toMetric.ball x ε := by
  intro y hy
  have h : supNorm.norm (x - y) < ε / 2 := hy
  have h2 := taxicab_le_two_supNorm (x - y)
  show taxicab.norm (x - y) < ε
  linarith

/-! @end -/

end GeneralTopology
