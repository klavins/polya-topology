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

The five built sections measure 4 to 7 concepts and 9 to 31 problems, in 280 to 780 lines. That
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

§5 came in at 5 concepts, 16 problems and 460 lines, with the longest proof at twelve. It needed
no new import at all, which is what the previous section's fence growth had already bought.

§6 came in at 4 concepts, 18 problems and 603 lines, with the longest proof at eleven and the
longest declaration — a six-field structure instance — at thirteen. Four concepts and eighteen
problems is the other end of the range from §4's five and eighteen: a section is sized by its
problems, not by its concepts, and a concept that carries five of them is not too big.

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

- [x] **5. Continuous Functions** — `Continuity.lean` · 5 concepts, 16 problems

  The ε-δ definition in a metric space, at a point and everywhere; continuity without distances,
  as openness of preimages, with the identity, the constants and composition; the theorem that the
  two agree; the closed-set form, the closure form and the pointwise form; and the definition
  tested on the discrete, codiscrete, Sierpiński and subspace topologies.

  Concepts: `epsilon_delta`, `continuous_maps`, `continuity_bridge`, `continuity_closed`,
  `continuity_examples`.

  As built, and what it settled:

  - The **`@goal` moved** from §4's `dense_sets` to `continuity_examples`.
  - **The bridge was not expensive.** The flag budgeted a helper problem in each direction; neither
    was wanted. Each direction is four lines, because §1 and §2 had already done the translating:
    a membership in a ball *is* the distance inequality it abbreviates, and `Metric.toTopology`
    calls open exactly what the metric does, so the ε-δ data and the open-set data are the same
    data and the proof only rearranges it. The remaining entry in "the four expensive proofs" list
    below should be read with that in mind — a proof looks expensive until the definitions line up.
  - **Two universes, at last.** `Topology.Continuous` relates a topology on `X` to one on `Y`, and
    `sierpinski : Topology Bool` puts `Bool` at `Type 0` against an arbitrary `X : Type u`. So the
    four continuity definitions and the theorems about them carry `{X : Type u} {Y : Type v}`, and
    `continuous_comp` carries a third. The "keep both factors in `Type u`" note under **Shapes that
    cost more than they look** is hereby spent: §7's products and §8's sums should follow suit
    rather than forcing one universe. The cost is one binder per signature and the stub shows it,
    so it costs the student nothing.
  - **The Sierpiński classification is two problems, not one.** That a map `X → Bool` is continuous
    exactly when `f ⁻¹' {true}` is open needs to know that the space has only three open sets, and
    the trichotomy is a `Bool` case analysis that would push the main proof past fifteen lines. Split
    out, it is six lines — `by_cases` twice, and `cases b` inside each — and it is a real statement
    about the space rather than the membership tedium rule 6 warns against.
  - `continuous_closure` came out at seven lines, as §4's flag predicted: `Set.image_subset_iff` and
    then `T.closure_min`, with the preimage of a closed set closed.

---

- [x] **6. Homeomorphisms** — `Homeomorphisms.lean` · 4 concepts, 18 problems

  When two spaces are the same space: a bundled bijection continuous in both directions, with the
  identity, the inverse and the composite that make being homeomorphic an equivalence relation;
  open maps and closed maps, and the test they give for when a continuous bijection is one; two
  metrics whose balls fit inside each other's, and the plane measured two ways shown to be one
  space; and two properties a homeomorphism transports, with which the three topologies on a
  two-point set are told apart.

  Concepts: `homeomorphism`, `open_closed_maps`, `metric_equivalence`, `topological_invariants`.

  As built, and what it settled:

  - The **`@goal` moved** from §5's `continuity_examples` to `topological_invariants`.
  - **No new import, for the second section running.** The fence has not grown since §4, so §7's
    `Mathlib.Data.Set.Prod` will be the first addition in three sections.
  - **A bijection is presented by its inverse map**, never by `Function.Bijective` and never by
    choosing an inverse out of surjectivity. `Homeomorphism.ofOpenMap` takes a `g` with
    `∀ x, g (f x) = x` and `∀ y, f (g y) = y`, which is what the structure's own fields already
    are, so no statement downstream has to carry a `Classical.choose`. §7's and §8's universal
    properties should be stated the same way. That a homeomorphism's forward map *is* a bijection
    is a two-line problem (`Homeomorphism.injective`, `.surjective`), and that is where the word
    is earned.
  - `image_eq_preimage_of_inverse` — that `f '' U = g ⁻¹' U` for mutually inverse `f` and `g` — is
    the one equation the whole of `open_closed_maps` rests on. It is stated for a bare pair of maps
    rather than for a homeomorphism, so that `ofOpenMap` can use it before there is a homeomorphism
    to use it on.
  - **The invariants are discreteness and codiscreteness, not a count of the maps into Sierpiński.**
    The flag proposed the latter. The two properties are cheaper: each transports in three lines
    along `Homeomorphism.isOpen_iff`, and between them they separate all three topologies on `Bool`
    pairwise, which counting would have needed a bijection between two families of open sets to do.
    `Homeomorphism.isOpen_iff` and `Homeomorphism.preimage_preimage` are the tools §9 and §13
    should transport a property with; neither needs restating there.
  - The source's counterexample to "a continuous bijection is a homeomorphism" is `[0,2π) → S¹`,
    which needs the circle. The identity from `discrete Bool` to `codiscrete Bool` carries the same
    lesson inside the fence, and it is §5's `continuous_from_discrete` plus the last problem of this
    section, so it costs nothing.
  - **Three universes**, as `continuous_comp` already needed: `Homeomorphism.trans` relates three
    spaces. §5's note stands and §7 and §8 should follow it.
  - Only the **open**-map form of "a continuous bijection is a homeomorphism" is built. §13's
    `compact_to_hausdorff` wants the closed-map form; it is the same proof with `Set.preimage_compl`
    in the middle, and it belongs there, where the hypothesis that supplies a closed map is.

- [ ] **7. Subspaces and Products** — `Products.lean` · 5 concepts, ~16 problems

  The first constructions that make new spaces from old. Builds on §3's subspace and §5.

  - `subspace_maps` — a map into a subspace is continuous exactly when its composite with the
    inclusion is; the closed sets of a subspace are the traces of closed sets; a subspace of a
    subspace. **That the inclusion is continuous is already built** — §5's
    `Topology.continuous_subspace_val`, with `Topology.continuous_restrict` beside it — so cite
    those rather than restating them, and spend the room on the universal property instead.
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
  one. Fence grows by `Mathlib.Data.Set.Prod` (tested clean) — and, per the fence flag below, that
  import widens the whole subject's fence, so test it against the five forbidden names first.
  A product of two spaces at `Type u` and `Type v` lands in `Type (max u v)`; §5 already pays the
  two-universe cost in every continuity signature and §6's `Homeomorphism.trans` pays a third, so
  follow them rather than forcing one universe. `plane_is_product` is a homeomorphism, and §6 has
  the vocabulary for it: state it as `Homeomorphic`, build it with `Homeomorphism.ofOpenMap` or by
  naming the two maps directly, and compose with `plane_homeomorphic` for the taxicab case rather
  than repeating the comparison of balls. A construction's universal property — "a map into the
  product is continuous exactly when both components are" — is stated with the maps themselves, in
  §6's manner: never `Function.Bijective`, never an inverse chosen out of surjectivity.

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

  Flags: each axiom is a topological invariant, and §6 built the machine for saying so —
  `Homeomorphism.isOpen_iff` with `Homeomorphism.preimage_preimage` beside it. If a problem here
  wants "a space homeomorphic to a Hausdorff space is Hausdorff", it is those two and a transport
  of points, in the shape of `Homeomorphic.isCodiscrete`; do not restate them.
  `separation_closures` is stated in §4's vocabulary throughout — `T.mem_closure_iff` is
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

  Flags: `compact_to_hausdorff`'s second half — a continuous bijection between them is a
  homeomorphism — is the closed-map form of §6's `Homeomorphism.ofOpenMap`, which §6 deliberately
  did not build: it is that definition with `Set.preimage_compl` in the middle, and it belongs
  here, where the hypothesis that makes the map closed lives. Present the bijection as §6 does,
  by the map that undoes it.
  `heine_borel` is `interval_compact` plus `compact_basics` plus `compact_metric`, so it
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
is the one thing that is not. Neither §5 nor §6 needed an addition, and the fence has not moved
since §4. Test any further import before adding it; the command is in
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
- `Metric.ContinuousAt`, `Metric.Continuous`, `Topology.Continuous`, `Topology.ContinuousAt`,
  `Topology.continuous_id`, `Topology.continuous_const`, `Topology.continuous_comp`,
  `Metric.continuous_iff`, `Topology.continuous_iff_closed`, `Topology.continuous_closure`,
  `Topology.continuous_iff_continuousAt`, `Topology.continuous_subspace_val`,
  `Topology.continuous_restrict`, `continuous_from_discrete`, `continuous_to_codiscrete`,
  `sierpinski_open_cases`, `sierpinski_continuous_iff`, `line_continuous_affine`
- `Homeomorphism` (with `toFun`, `invFun`, `left_inv`, `right_inv`, `continuous_toFun`,
  `continuous_invFun`), `Homeomorphism.refl`, `.symm`, `.trans`, `.injective`, `.surjective`,
  `.image_eq_preimage`, `.isOpenMap`, `.isClosedMap`, `.ofOpenMap`, `.preimage_preimage`,
  `.isOpen_iff`; `Homeomorphic` and `Homeomorphic.refl`, `.symm`, `.trans`, `.isDiscrete`,
  `.isCodiscrete`; `image_eq_preimage_of_inverse`
- `Topology.IsOpenMap`, `Topology.IsClosedMap`, `Topology.IsDiscrete`, `Topology.IsCodiscrete`,
  `discrete_isDiscrete`, `codiscrete_isCodiscrete`, `singleton_true_not_trivial`,
  `sierpinski_not_discrete`, `sierpinski_not_codiscrete`
- `Metric.Equivalent`, `Metric.isOpenSet_of_ball_subset`, `Metric.Equivalent.isOpenSet_iff`,
  `Metric.Equivalent.toHomeomorphism`, `taxicab_equivalent_supNorm`, `plane_homeomorphic`

Two in particular: §7's `induced_topology` is the shape `Topology.subspace` already has
(`∃ U, T.IsOpen U ∧ V = f ⁻¹' U`), so the subspace topology is a *case* of it, proved by `rfl`;
and §4's `interior_boundary` must build on §2's `union_of_opens_inside`, which is the statement
that an open set is its own interior.

### What the closure can see

`polya extract` builds each problem's preamble by walking the tokens of its reference and by
asking the build what the target depends on. A declaration that arrives as *context* — one the
problem never names, but that came in beside something it does — is then closed over its own
tokens alone, and **dot notation on a local variable is not a token the walk can resolve**:
`T.continuous_id`, with `T : Topology X`, names `Topology.continuous_id` through the *type* of
`T`, and nothing in the text says so. A structure's *fields* are safe, since they arrive with
the structure; a theorem that merely lives in the same namespace is not.

So a declaration that a later problem is likely to pull as context writes its citations in full.
§6's `Homeomorphism.refl` and `.trans` say `Topology.continuous_id T` and
`Topology.continuous_comp T`, not `T.continuous_id` and `T.continuous_comp`: with the dot form,
both problems of `metric_equivalence` failed to close at all, reporting an "invalid field" error
inside a declaration they never mention. Only the reference's spelling changes — a student who
writes the dot form still passes, since the spec checks the data fields — so the cost is nil.
§5's `Topology.continuous_restrict` has the same shape and has not been pulled anywhere yet; if a
later section stalls this way, that is the first place to look.

### Shapes that cost more than they look

- **Generating a topology from a family.** Avoid it — see §7. Every construction in §7 and §8 is
  defined directly instead, and each is a short `where`-bodied definition of the same shape as
  `Metric.toTopology`.
- **Subsets versus subspaces.** Compactness and connectedness are each stated twice in the
  literature — of a space, and of a subset. Define the subset version with opens of the ambient
  space, prove once that it agrees with the subspace being compact or connected, and never juggle
  subtypes again.
- **Quotients.** `Quot.lift`'s obligations are where a draft will stall; §8's flag says how.
- **Universes.** §1 to §4 are all `Type u`. §5 is not, and could not be: `Topology.Continuous`
  relates a topology on `X` to one on `Y`, and `sierpinski : Topology Bool` puts `Bool` at
  `Type 0` against an arbitrary `X : Type u`, so the continuity definitions carry
  `{X : Type u} {Y : Type v}` and `continuous_comp` carries a third. Every later construction
  relating two spaces should do the same from the start rather than forcing one universe and
  discovering the clash at the first concrete example. The noise is one binder per signature, the
  stub shows it, and it costs the student nothing.
- **Choice and computability.** `Classical.choice` is on the check's axiom allowlist, so `choose`
  and proof by contradiction are available, and a `noncomputable def` — which an infimum over a
  set of reals forces — passes the extractor's command allowlist.

### The expensive proofs

In the order they arise, these are the ones to budget for and to split into helper problems:
§10's connectedness of an interval; §11's two reverse halves, which pick a point from each of a
shrinking sequence of balls; and, far above the rest, §12's compactness of a closed interval.

§5's bridge between ε-δ and open sets was on this list and is struck from it: built, it is ten
lines and wanted no helper, because §1's balls and §2's `Metric.toTopology` had already made the
two sides the same data. Take the remaining three as estimates of the same kind — a proof looks
expensive until the definitions line up, and the way to find out is to write the statement and
see what the earlier sections hand over.
