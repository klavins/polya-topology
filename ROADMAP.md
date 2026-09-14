# Roadmap for `generaltopology`

What the subject is to contain, section by section, and in what order. The outline follows Urs
Schreiber's *Introduction to Topology — 1* on the
[nLab](https://ncatlab.org/nlab/show/Introduction+to+Topology+--+1), which supplies the selection
and the order of the results; the prose, the Lean and the problems are written here.

The source is a research-level survey and runs to vector bundles and smooth manifolds. This
roadmap stops where the fence does — see **Flags** below and `STYLE.md` — and says plainly which
of the source's results are out of reach and why.

One departure from the source's order is already made and is kept: the source proves continuity
in metric spaces *before* abstracting to topological spaces, whereas §2 abstracts first and §5
treats continuity in both settings at once, with the theorem that the two agree. Everything else
follows the source.

## How a section is sized

The four built sections measure 4 to 7 concepts and 9 to 31 problems, in 280 to 780 lines. That
is the target: **five or six concepts and twelve to eighteen problems**, which is a section a
coding agent can draft, compile and extract in one sitting. A section wanting more than that is
two sections. Every proof stays under fifteen lines; where a step will not, the step becomes a
problem of its own, taught before the problem that needs it.

§4 came in at 5 concepts, 18 problems and 497 lines, with the longest proof at fourteen. Two of
its problems carry three declarations apiece — the three properties that characterise the
closure, and the three that characterise the interior — which is a shape the earlier sections
did not use and which is worth reusing wherever a construction is pinned by a universal
property: the parallel between the two is the lesson, and splitting it across six problems
would hide it.

## The sections

- [x] **1. Metric Spaces** — `MetricSpaces.lean` · 7 concepts, 31 problems

  The axioms and the two facts they do not ask for; open and closed balls and spheres; bounded
  sets; norms and the metric a norm induces; the taxicab and supremum norms on the plane and the
  fact that each one's balls fit inside the other's.

  Concepts: `metric_space`, `real_line`, `open_ball`, `bounded_set`, `normed_space`,
  `norm_metric`, `plane_norms`.

- [x] **2. Topological Spaces** — `TopologicalSpaces.lean` · 5 concepts, 13 problems

  The sets a metric calls open and the three properties they have; those three properties taken
  as a definition; every metric space as a topological space; closed sets; neighbourhoods, and
  openness as a property holding at each point.

  Concepts: `open_sets`, `topological_space`, `metric_topology`, `closed_sets`, `neighbourhoods`.

- [x] **3. Basic Examples** — `BasicExamples.lean` · 4 concepts, 9 problems

  The two extremes that bound every topology on a set; the Sierpiński space; the cofinite
  topology; the subspace topology.

  Concepts: `extreme_topologies`, `sierpinski_space`, `cofinite_topology`, `subspace_topology`.

- [x] **4. Closure, Interior and Boundary** — `Closure.lean` · 5 concepts, 18 problems

  The two duals §2 left; the smallest closed set around a set and the largest open set inside it,
  each pinned by three properties and each the complement of the other; a point of the closure as
  a point the set is found arbitrarily near, with neighbourhoods and then with balls; the boundary,
  and its emptiness as the test for open-and-closed; dense sets, and the rationals in the line.

  Concepts: `closed_families`, `closure`, `closure_points`, `interior_boundary`, `dense_sets`.

  As built, and what it settled:

  - The **`@goal` moved** from §3's `subspace_topology` to `dense_sets`. A subject carries exactly
    one, and it belongs on the last concept of the last section; every later section moves it again.
  - `closure_union` — the closure of a union of two sets is the union of the closures — was not in
    the plan and is in the section. It is the source's proposition, it falls straight out of the
    three properties, and without it the concept is all plumbing. The infinite analogue is false;
    the preamble says so and asks nothing.
  - Only one half of the duality is built, `(T.closure S)ᶜ = T.interior Sᶜ` (`compl_closure`). The
    other half is that one at `Sᶜ` with a `compl_compl`; a later section that wants it should prove
    it there rather than reopening this one.
  - `Metric.mem_closure_iff` states the ball form against `M.toTopology`, so §11's
    `sequential_closure` has its bridge already and owes only the choice of a point from each ball.
  - `is_open_iff_interior_eq` is proved from §2's `union_of_opens_inside`, as the flag asked, so
    nothing was restated.

---

- [ ] **5. Continuous Functions** — `Continuity.lean` · 5 concepts, ~16 problems

  The maps a topology admits. Builds on §1 (balls), §2, §3 (the three example topologies) and §4.

  - `epsilon_delta` — continuity of a map between metric spaces at a point and everywhere;
    constants, the identity, and an affine map of the line.
  - `continuous_maps` — continuity as: the preimage of every open set is open. The identity,
    constants, and the composite of two continuous maps.
  - `continuity_bridge` — for metric spaces the two definitions agree. The theorem of the section.
  - `continuity_closed` — equivalently, the preimage of every closed set is closed; a continuous
    map carries the closure of a set into the closure of its image; continuity at a point, stated
    with neighbourhoods.
  - `continuity_examples` — every map out of a discrete space and every map into a codiscrete one
    is continuous; a map to the Sierpiński space is continuous exactly when the preimage of the
    open point is open, so that space classifies open sets; the inclusion of a subspace is
    continuous.

  Flags: the bridge is the longest proof here and may want a helper problem in each direction.
  §4 left `continuity_closed` most of its work done: "carries the closure into the closure of the
  image" is `T.closure_min` applied to the preimage of the target's closure, which is closed by
  the concept's own first result and contains the set — three lines, not a section's worth. The
  `@goal` sits on §4's `dense_sets` and moves here, to this section's last concept. This is also
  the section that makes density worth having, so `continuity_examples` is the natural home for
  the remark that two continuous maps agreeing on a dense set agree everywhere — if it is proved,
  it needs Hausdorff and so belongs after §9, not here.

- [ ] **6. Homeomorphisms** — `Homeomorphisms.lean` · 4 concepts, ~12 problems

  When two spaces are the same space. Builds on §5.

  - `homeomorphism` — a bundled bijection continuous in both directions, in the house style of
    §1's `Metric` and `Norm`: a structure carried as an argument, with no instances. The identity,
    the inverse, and the composite, so that being homeomorphic is an equivalence relation.
  - `open_closed_maps` — open maps and closed maps; a continuous open bijection is a
    homeomorphism, and a homeomorphism is an open map.
  - `metric_equivalence` — two metrics whose balls fit inside each other's induce the same
    topology, so the identity is a homeomorphism; hence the taxicab and the supremum metric on
    the plane, whose unit balls are visibly different sets, are the same space. This is what §1's
    last two problems were for.
  - `topological_invariants` — a property preserved by homeomorphism, and the use of one to tell
    two spaces apart: the discrete and codiscrete topologies on a two-point set, and Sierpiński
    between them.

  Flags: the source's examples here — the open interval homeomorphic to the line, stereographic
  projection, the circle as a glued interval — need rational or transcendental functions and, for
  the last two, a square root. They are not available; the metric-equivalence example above
  carries the same lesson and costs nothing.

- [ ] **7. Subspaces and Products** — `Products.lean` · 5 concepts, ~16 problems

  The first constructions that make new spaces from old. Builds on §3's subspace and §5.

  - `subspace_maps` — the inclusion is continuous; a map into a subspace is continuous exactly
    when its composite with the inclusion is; the closed sets of a subspace are the traces of
    closed sets; a subspace of a subspace.
  - `induced_topology` — the same construction along any map: the opens are the preimages of
    opens. The subspace topology of §3 is this, for the inclusion — an identification, not a new
    definition.
  - `product_topology` — the topology on a product of two spaces, defined pointwise as §2 defined
    the open sets of a metric: a set is open when each of its points has a box around it inside.
    That it is a topology, and that boxes are open.
  - `product_maps` — the projections are continuous and open; a map into a product is continuous
    exactly when both of its components are.
  - `plane_is_product` — the supremum metric on the plane induces the product of two copies of
    the line, because a supremum ball *is* a box; with §6 the taxicab metric induces it too. The
    capstone of everything built about the plane.

  Flags: do **not** define "the topology generated by a family of sets". With `Topology` a bundled
  structure, generation needs either an inductive definition or an intersection over all
  topologies containing the family, and the latter needs a lattice structure on `Topology X` that
  nothing else in the subject wants. Define each construction directly, as §2 did. A *basis* can
  still be had cheaply as a property — every open is a union of members — and boxes shown to be
  one. Fence grows by `Mathlib.Data.Set.Prod` (tested clean).

- [ ] **8. Quotients and Sums** — `Quotients.lean` · 4 concepts, ~12 problems

  The constructions dual to the last section's. Builds on §7.

  - `final_topology` — the topology along a map in the other direction: a set is open below
    exactly when its preimage is open above. It is a topology because preimage commutes with
    everything; the map is continuous; a map out of it is continuous exactly when its composite
    with the map is.
  - `quotient_space` — the quotient by an equivalence relation, as the final topology along the
    quotient map; saturated sets; the quotient of a discrete space is discrete.
  - `sum_space` — the disjoint union of two spaces: a set is open when both of its preimages are;
    the two injections are continuous open maps; a map out of a sum is a pair of maps.
  - `quotient_examples` — collapsing a subset to a point, and the quotient of the line by a closed
    interval.

  Flags: this is the section with the most Lean friction and the thinnest examples inside the
  fence — the source's quotients of interest (the circle, the cylinder, the Möbius strip, the
  torus) are all beyond it. Keep every statement about a quotient phrased through `Quot.mk` and
  `Quot.lift` rather than by choosing representatives. Nothing after this section depends on it,
  so it can be deferred past §13 without disturbing the order.

- [ ] **9. Separation Axioms** — `Separation.lean` · 5 concepts, ~15 problems

  How well a topology tells points apart — the first thing asked of a space once it exists.
  Builds on §4 (closures), §7 (subspaces and products) and §3 (the examples that fail).

  - `separation_axioms` — the first three axioms, and that each implies the one before.
  - `separation_examples` — every metric space is Hausdorff, by halving the distance; the
    codiscrete topology is not even the first; Sierpiński is the first and not the second; the
    cofinite topology on the naturals is the second and not the third.
  - `separation_closures` — the axioms restated with closures: points are closed exactly in a
    T₁ space, distinct points have distinct closures exactly in a T₀ space, and a space is
    Hausdorff exactly when the diagonal is closed in the product. The last is §7's payoff.
  - `separation_hereditary` — a subspace of a T_n space is T_n, and a product of two of them is.
  - `regular_normal` — the two stronger axioms stated, with the easy cases: a discrete space is
    normal, and a metric space is regular.

  Flags: `separation_closures` is stated in §4's vocabulary throughout — `T.mem_closure_iff` is
  the tool for all three, and "points are closed" is `T.isClosed_iff_closure_eq` at a singleton.
  "every metric space is normal" wants the distance from a point to a set, an infimum over
  a set of reals. It is available (`sInf`, with the definition marked `noncomputable`, which the
  extractor accepts) but it costs a concept of its own; leave it out unless the section is short.
  Urysohn's lemma is out of scope — see the last section below.

- [ ] **10. Connectedness** — `Connectedness.lean` · 5 concepts, ~14 problems

  The first property that is about the whole space rather than its points. Builds on §5 and §7.

  - `connected` — a space is connected when the only sets both open and closed are the empty one
    and everything; equivalently it is not two nonempty disjoint opens. Stated for a subset as
    well as for a space, and the two shown to agree once.
  - `connected_examples` — the codiscrete space is connected and a two-point discrete space is
    not; an interval of the line is connected. The second is where the least-upper-bound property
    enters the subject.
  - `connected_images` — the continuous image of a connected space is connected; hence the
    intermediate value theorem, which is that sentence applied to the line.
  - `components` — the connected component of a point; components are closed and partition the
    space; a totally disconnected space; the components of a discrete space are its points.
  - `path_connected` — a path as a continuous map from the unit interval; path-connected implies
    connected; the line and the plane are path-connected, by affine paths.

  Flags: "the connected subsets of the line are exactly the intervals" is two theorems, and only
  the easy half — an interval is connected — is worth a problem; say the converse in prose. The
  standard proof that the rationals are totally disconnected wants an irrational number to cut
  them at, and the usual witness is a square root, which the fence excludes; use the discrete
  example instead. `path_connected` is the first concept to drop if the section runs long.

- [ ] **11. Sequences and Convergence** — `Sequences.lean` · 5 concepts, ~14 problems

  What the source treats first, and what reads better here, where closures and the separation
  axioms are already available to say what a limit is and when it is unique. Builds on §1, §4,
  §5 and §9.

  - `convergence` — a sequence converging to a point of a metric space; constant sequences;
    a sequence has at most one limit, by the triangle inequality.
  - `convergence_topological` — the same with neighbourhoods in place of balls; the two agree for
    a metric; in a codiscrete space every sequence converges to every point, and limits are unique
    exactly when the space is Hausdorff.
  - `sequential_closure` — in a metric space a point lies in the closure of a set exactly when
    some sequence in the set converges to it.
  - `sequential_continuity` — a continuous map carries convergent sequences to convergent
    sequences, and for metric spaces the converse holds.
  - `cauchy_complete` — Cauchy sequences; every convergent sequence is Cauchy; a complete metric
    space; a discrete metric space is complete.

  Flags: `sequential_closure` is §4's `Metric.mem_closure_iff` turned into a sequence and back,
  so the section inherits the ball form and owes only the sequence. The reverse halves of
  `sequential_closure` and `sequential_continuity` pick a point from
  each ball of radius `1/(n+1)`, so they use `choose` and the Archimedean property, which §4 put
  in the fence for good. Both are fine
  — `Classical.choice` is on the check's axiom allowlist — but they are the two longest proofs in
  the section. That the line is complete is a real theorem, not a corollary of anything here;
  leave it stated in prose, or give it a section of its own later.

- [ ] **12. Compactness** — `Compactness.lean` · 5 concepts, ~15 problems

  The property that makes infinite covers finite, and the last of the three big ones. Builds on
  §7, §9 and §10.

  - `open_cover` — covers, subcovers, and a compact space; compactness of a subset, phrased with
    opens of the ambient space, and shown once to agree with compactness of the subspace.
  - `compact_basics` — a finite space is compact; a finite union of compact subsets is compact;
    a closed subset of a compact space is compact.
  - `compact_images` — the continuous image of a compact space is compact; hence a continuous
    real function on a compact space is bounded, and attains its bounds.
  - `compact_metric` — a compact subset of a metric space is bounded, and — once §9 is in hand —
    closed.
  - `interval_compact` — a closed interval of the line is compact.

  Flags: `interval_compact` is the single most expensive item in this roadmap. The proof is the
  least-upper-bound argument on the set of points up to which a finite subcover exists, and it
  wants three or four helper problems of its own; budget it as half the section, or give it a
  section. Everything else here is cheap. The extreme value theorem needs a supremum and the fact
  that it is attained — worth a helper.

- [ ] **13. Compact Hausdorff Spaces** — `CompactHausdorff.lean` · 5 concepts, ~13 problems

  Where compactness and separation meet, and the results that make compact Hausdorff spaces the
  well-behaved corner of the subject. Builds on §9 and §12.

  - `compact_in_hausdorff` — a compact subset and a point outside it are separated by
    neighbourhoods; hence a compact subset of a Hausdorff space is closed.
  - `compact_to_hausdorff` — a continuous map from a compact space to a Hausdorff space is a
    closed map; a continuous bijection between them is a homeomorphism.
  - `compact_normal` — a compact Hausdorff space is normal.
  - `tube_lemma` — the tube lemma, and the product of two compact spaces is compact.
  - `heine_borel` — on the line, and on the plane with the supremum metric, compact means closed
    and bounded.

  Flags: `heine_borel` is `interval_compact` plus `compact_basics` plus `compact_metric`, so it
  is cheap *if* §12 landed. The plane case needs §7's identification of the supremum metric with
  the product.

## What is deliberately left out

The source continues past where this roadmap stops. These are the results that will not be built,
and why:

| what | why not |
|---|---|
| Euclidean space, spheres, disks, the circle, stereographic projection, `p`-norms for `1 < p < ∞` | all need `Real.sqrt`, which is outside the fence (`STYLE.md`) |
| Sober spaces, frames of opens, sober reflection, T_n reflection | formalizable inside the fence, and specialized; a candidate for a *second subject* rather than a section of this one |
| Limits and colimits in the category of spaces | the source's framing is categorical; §7 and §8 state each universal property concretely instead, and `Mathlib.CategoryTheory` is not to be imported |
| Tychonoff's theorem for infinite products | needs Zorn's lemma or ultrafilters, and an infinite product needs a generated topology, which §7 rules out |
| Urysohn's lemma, partitions of unity, paracompactness | the dyadic construction is a section on its own, and partitions of unity need bump functions, hence analysis |
| Local compactness, one-point compactification, mapping spaces and the compact-open topology | reachable in principle; a later roadmap's business, once §13 is in |
| Sequential compactness equivalent to compactness for metric spaces | needs completeness and total boundedness, both of which are theorems this subject has not built |
| Cell complexes, vector bundles, manifolds, tangent bundles | the source's part 2; needs analysis and smoothness, so out of reach entirely |

## Flags

### The fence

The rule is `STYLE.md`'s: `MetricSpace`, `Metric.ball`, `IsOpen`, `TopologicalSpace` and
`Continuous` must all be unknown identifiers under a section's imports. Tested against
Mathlib `v4.31.0`, on 2026-09-13:

| module | verdict |
|---|---|
| `Mathlib.Data.Set.Prod`, `Mathlib.Data.Set.Image`, `Mathlib.Data.Set.Finite.Lattice`, `Mathlib.Data.Set.Card` | clean |
| `Mathlib.Order.Interval.Set.Basic`, `Mathlib.Order.Bounds.Basic`, `Mathlib.Order.ConditionallyCompleteLattice.Basic`, `Mathlib.Order.CompleteLattice.Basic`, `Mathlib.Order.Zorn`, `Mathlib.Order.Filter.Basic` | clean |
| `Mathlib.Algebra.Order.Archimedean.Real.Basic` | clean — gives `Real.isLUB_sSup`, `exists_rat_btwn`, `exists_nat_gt` |
| `Mathlib.Data.Finset.Max`, `Mathlib.Data.Fintype.Basic`, `Mathlib.Data.Nat.Lattice`, `Mathlib.Data.Countable.Basic` | clean |
| `Mathlib.Logic.Equiv.Basic`, `Mathlib.Data.Prod.Basic`, `Mathlib.Data.Sum.Basic` | clean |
| `Mathlib.Data.Real.Sqrt`, and everything under `Mathlib.Analysis.*` | **reaches topology** — all five names resolve |

So the fence is roomier than it looks: the least-upper-bound property, the Archimedean property,
intervals, finite sets, products of sets and Zorn's lemma are all available, and the square root
is the one thing that is not. Test any further import before adding it; the command is in
`STYLE.md`, and the message to grep for is `unknownIdentifier`, which Lean capitalizes.

`Mathlib.Data.Real.Archimedean` is **deprecated** in this toolchain and emits a warning naming
its replacement. Warnings are errors under publish, so import
`Mathlib.Algebra.Order.Archimedean.Real.Basic` instead. Two more names that look innocent are
deprecated the same way: `Set.diff_eq_empty` and `Set.diff_self`, whose replacements are
`Set.sdiff_eq_empty` and `Set.sdiff_self`.

**The fence is the subject's, not the section's.** `polya extract` accumulates the imports of
every section file into one list and compiles *every* problem against all of it, so an import
added in a late section widens the fence of the first section too. §4's
`Mathlib.Algebra.Order.Archimedean.Real.Basic` is therefore already in scope for §1, and with it
`Real.isLUB_sSup`, `exists_rat_btwn` and `exists_nat_gt`: §10's connected interval, §11's
shrinking balls and §12's closed interval need no further import, and their flags below should
be read as already paid. The widening is silent — the environment row is keyed by slug and its
module list is rewritten in place, so the publish that added it reported **0 problems
versioned** and no student was moved. The consequence to watch is the other way round: a module
imported for one problem in §12 is a module every problem in §1 may close itself with. Test a
candidate import against the five forbidden names as before, but weigh it against the whole
subject, not against the section asking for it.

### Names already taken

Nothing below is to be defined a second time. Where a later section generalizes one of these, the
generalization is an identification — a `theorem` or an `example` saying the old thing is the new
one — never a redefinition.

- `Metric`, `Metric.ball`, `Metric.closedBall`, `Metric.sphere`, `Metric.IsBounded`,
  `Metric.IsOpenSet`, `Metric.toTopology`, `line`
- `Norm`, `Norm.toMetric`, `absNorm`, `taxicab`, `supNorm`
- `Topology`, `Topology.IsClosed`, `Topology.IsNbhd`, `Topology.subspace`
- `discrete`, `codiscrete`, `cofinite`, `sierpinski`
- `Topology.closure`, `Topology.interior`, `Topology.boundary`, `Topology.Dense`,
  `Topology.closure_min`, `Topology.interior_max`, `Topology.mem_closure_iff`,
  `Metric.mem_closure_iff`, `Topology.dense_iff`, `Topology.compl_closure`, `rationals`

Two in particular: §7's `induced_topology` is the shape `Topology.subspace` already has
(`∃ U, T.IsOpen U ∧ V = f ⁻¹' U`), so the subspace topology is a *case* of it, proved by `rfl`;
and §4's `interior_boundary` must build on §2's `union_of_opens_inside`, which is the statement
that an open set is its own interior.

### Shapes that cost more than they look

- **Generating a topology from a family.** Avoid it — see §7. Every construction in §7 and §8 is
  defined directly instead, and each is a short `where`-bodied definition of the same shape as
  `Metric.toTopology`.
- **Subsets versus subspaces.** Compactness and connectedness are each stated twice in the
  literature — of a space, and of a subset. Define the subset version with opens of the ambient
  space, prove once that it agrees with the subspace being compact or connected, and never juggle
  subtypes again.
- **Quotients.** `Quot.lift`'s obligations are where a draft will stall; §8's flag says how.
- **Universes.** Everything built so far is `Type u`. A product of spaces at two different
  universes lands in `Type (max u v)`, which is fine but noisy in every signature; keep both
  factors in `Type u` unless a problem genuinely needs otherwise.
- **Choice and computability.** `Classical.choice` is on the check's axiom allowlist, so `choose`
  and proof by contradiction are available, and a `noncomputable def` — which an infimum over a
  set of reals forces — passes the extractor's command allowlist.

### The four expensive proofs

In the order they arise, these are the ones to budget for and to split into helper problems:
§5's bridge between ε-δ and open sets; §10's connectedness of an interval; §11's two reverse
halves, which pick a point from each of a shrinking sequence of balls; and, far above the rest,
§12's compactness of a closed interval.
