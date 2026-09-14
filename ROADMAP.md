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

The eight built sections measure 4 to 7 concepts and 9 to 31 problems, in 280 to 780 lines. That
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

§7 came in at 5 concepts, 17 problems and 513 lines, with the longest proof at ten and the
longest single field of a structure — the intersection condition of the product topology — at
nine. Five sections running have landed between 16 and 18 problems, so the range at the top of
this note can be narrowed: **five concepts and sixteen to eighteen problems** is what a section
is, and the two that fell outside it (§1's 31, §3's 9) are the first section and the shortest.

§8 came in at 5 concepts, 20 problems and 578 lines, with the longest proof at eleven and the
longest declaration — the four fields of the sum topology — at seventeen. It is the first
overshoot of the narrowed range, and the cause is nameable: one of its five concepts teaches a
piece of Lean (`Setoid` and `Quotient`) rather than a piece of topology, and a concept like that
is four problems whatever the mathematics around it costs. Count such a concept against the
budget like any other. **Five concepts and sixteen to eighteen problems** still stands.

§9 came in at 5 concepts, 18 problems and 584 lines, with the longest proof at fourteen. Two of
its eighteen problems exist only to keep a proof under fifteen lines — a positive distance between
distinct points, and the two facts about the closure of a single point — which is the cost the
line limit charges, and it is paid in problems, not in prose. Budget one such helper per hard
statement rather than hoping the proof will fit.

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

- [x] **7. Subspaces and Products** — `Products.lean` · 5 concepts, 17 problems

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

  As built, and what it settled:

  - The **`@goal` moved** from §6's `topological_invariants` to `plane_is_product`.
  - **The fence grew for the first time since §4**, by `Mathlib.Data.Set.Prod` (tested against the
    five forbidden names first, as the flag asked). It widens the whole subject, so `×ˢ`,
    `Set.prod_univ`, `Set.univ_prod` and `Set.mem_prod` are now in scope for §1 as well.
  - **`Topology.eq_of_isOpen_iff` was not in the plan and is in the section.** Lean generates no
    `ext` lemma for `Topology` — the structure carries no `@[ext]` — so an equality of topologies
    could not be proved at all until one existed, and `induced_induced` wanted one. It is six
    lines: `obtain` both structures apart, `funext` and `propext` the two families of open sets,
    `subst`, `rfl`, the last step being definitional proof irrelevance on the three conditions.
    This is the tool for every later claim that two topologies are *equal* rather than
    homeomorphic; §8's quotient of a discrete space is the next one.
  - **The basis is a theorem, not a definition.** The flag offered `Topology.IsBasis` as a cheap
    property. What is built instead is the concrete statement — an open set of a product is the
    union of the open boxes inside it (`Topology.prod_eq_sUnion_boxes`) — which is the content
    without the vocabulary, and nothing in the section wanted the abstraction. Define `IsBasis`
    only when some section finds two users for it.
  - **"A subspace of a subspace" is `induced_induced`.** `(T.induced f).induced g` is
    `T.induced (f ∘ g)`, and that is the whole of it. Stated instead for a `B : Set A` against
    `Subtype.val '' B` it would have needed a homeomorphism between two subtypes and taught
    nothing; §9's hereditary axioms and §12's subset-versus-subspace should read it this way too.
  - **`Homeomorphism.ofOpenMap` was not wanted.** The two topologies on the plane turn out to have
    the *same* open sets, so the homeomorphism is the identity and its two continuities are the
    two directions of one equivalence — §6's `Metric.Equivalent.toHomeomorphism` exactly. A
    construction that does not move the points never needs an open-map argument.
  - **The projections are open by the neighbourhood criterion.** The source proves it from the
    basis, by images preserving unions. `Topology.isOpen_iff_nbhd` does it in six lines with no
    basis at all, and it is the tool for every "this image is open" proof here. §12's tube lemma
    should reach for it before reaching for boxes.
  - `Topology.continuous_toSubspace` — a continuous map all of whose values lie in `A` is
    continuous into `T'.subspace A`, written `fun x => (⟨f x, h x⟩ : A)` — was not in the plan and
    is in the section. §10's connected subsets and §12's compact subsets both want it; neither
    should restate it. `Topology.continuous_mk_left` and `.continuous_mk_right`, the slices, are
    there for §9's diagonal and §12's tube lemma on the same terms.
  - **A `where`-bodied definition's spec is `Iff.rfl`, so the order of its conjuncts is part of the
    answer.** `Topology.prod`'s description names the four in order for that reason. A student who
    writes `∀ p, p ∈ W → …` for `∀ p ∈ W, …` still passes — that was compiled against the spec —
    but one who reorders the conjuncts does not, and no tactic fixes that without weakening the
    check. Every later `where`-bodied definition should name its order the same way.
  - **`plane_is_product` was cheap**, which is the third time a flagged capstone has been. A
    supremum ball *is* a box by `max_lt_iff` and one `show`, and the rest is the two directions of
    an open-set comparison. Read the remaining estimates under **The expensive proofs** with that
    and §5's bridge in mind.

- [x] **8. Quotients and Sums** — `Quotients.lean` · 5 concepts, 20 problems

  The constructions dual to the last section's. Builds on §7.

  The topology along a map in the other direction: a set is open below exactly when its preimage
  is open above; that it is a topology, that the map is continuous, that it is the finest such,
  and that a map out of it is continuous exactly when the composite is. Then `Setoid` and
  `Quotient` in Lean, before any topology: the relation a map induces, that every element of a
  quotient is a class and when two classes are equal, and the map a function descends to. Then
  the quotient space as the final topology along the class map, its universal property,
  saturated sets, and the quotient of a discrete space. Then the disjoint union of two spaces,
  whose injections are continuous open maps and out of which a map is a pair of maps. The
  section ends by collapsing a subset of a space to a single point, and showing that the point
  a closed subset becomes is a closed point.

  Concepts: `final_topology`, `lean_quotients`, `quotient_space`, `sum_space`,
  `quotient_examples`.

  As built, and what it settled:

  - The **`@goal` moved** from §7's `plane_is_product` to `quotient_examples`.
  - **No new import at all**, in the section that was billed as the one with the most Lean
    friction. `Setoid`, `Quotient`, `Quotient.mk`, `.lift`, `.sound`, `.exact`,
    `.inductionOn`, `Sum`, `Sum.elim`, `Sum.inl_injective`, `Set.preimage_image_eq` and
    `Set.preimage_inr_image_inl` are all reachable under what §7 left, so the subject's fence is
    still the ten modules `polya extract` reports. The friction was not where it was expected.
  - **A concept of pure Lean, `lean_quotients`, placed before any topology.** It is the first
    concept since §1's `metric_space` with no prerequisites at all — it uses nothing the subject
    built — and it is on the goal's path only by the syllabus rule, because it is declared before
    the goal. A section that needs a piece of Lean machinery should do the same rather than
    teaching it inside the problem that first needs it.
  - **Favouring `Quotient` over `Quot` cost nothing.** Four names carry the whole of it:
    `Quotient.inductionOn` for "every element is a class", `Quotient.sound` and `Quotient.exact`
    for "two classes are equal exactly when the points are related", and `Quotient.lift` for a map
    out. `Quot.lift`'s raw obligations never appeared, and no proof chose a representative.
  - **A `Setoid` is passed explicitly, as a `Metric` is**, never as an instance, so the relation
    is written `s.r x y` and `≈` never appears in the subject. `Quotient.sound` and
    `Quotient.exact` still unify against it, since `a ≈ b` *is* `@Setoid.r _ s a b`. So the
    house rule "bundling, not classes" survives a class taken from core, and §11's convergence
    and §12's covers should assume the same of anything else core bundles as a class.
  - **`preimage_sUnion_image` was not in the plan and is in the section**, as its first problem.
    Mathlib's `Set.preimage_sUnion` produces an indexed union, and every construction here wants
    the `⋃₀` form, so the fact that a preimage carries a union of a family to the union of the
    preimages has to be proved once. Both `Topology.coinduced` and `Topology.sum` close their
    third field with it, and it is the one fact the section rests on.
  - **The coinduced topology is shorter than the induced one, as the flag predicted.** Its
    `IsOpen V` is `T.IsOpen (f ⁻¹' V)` with no existential, so there is nothing to take apart in
    any of the three fields. It is named `Topology.coinduced` rather than `Topology.final`, to
    pair with `Topology.induced`; the prose calls it the final topology.
  - **The quotient topology is a `def` with a term body** — `T.coinduced (Quotient.mk s)` — and
    everything about it is inherited rather than restated: the projection's continuity is
    `Topology.continuous_coinduced`, the universal property is
    `Topology.continuous_out_of_coinduced` at `Quotient.lift`, and the discrete case is the
    coinduced one. No field of a topology is written twice in this section.
  - **`quotient_discrete` is `fun _ => Iff.rfl`.** `Topology.eq_of_isOpen_iff` was the tool the
    flag named, but the two conditions turn out to be the same proposition and not merely
    equivalent, so the general statement — the final topology along *any* map out of a discrete
    space is discrete — costs the same as the quotient case and is built instead.
  - **`IsSaturated f S` is `S = f ⁻¹' (f '' S)` with no authored spec**, the orientation named in
    the description, as §7 established for definitions whose shape is the answer. What it buys is
    two lines: on an open saturated set the final topology's test asks about the preimage of the
    image, which is the set. §13's recognition of quotient projections is this with closed sets.
  - **The sum's universal property is free.** `Topology.continuous_sum_elim` is
    `fun W hW => ⟨hf W hW, hg W hW⟩`, because the preimage of a set under `Sum.elim f g`, read on
    either copy, *is* its preimage under that copy's map. The two injections' continuity is the
    same observation with `.1` and `.2`. Only their being open maps needed an argument, and that
    is `Set.preimage_image_eq` with `Sum.inl_injective` on the near side and
    `Set.preimage_inr_image_inl` on the far side.
  - **The examples are thin inside the fence, as the flag said, and the section stops where it
    should.** The quotient of the line by `[0,1]` is built, and what is proved of it is that the
    point the interval became is closed — which is `collapse_preimage_class` and one
    `Set.preimage_compl`. The line with two origins was left to §9, where the failure of Hausdorff
    is the point; it now costs only a second setoid, since `Topology.sum` and `Topology.quotient`
    are both here.
  - **Twenty problems, two above the band**, in 578 lines, with the longest proof at eleven
    (`unitInterval_closed`) and the longest declaration at seventeen (`Topology.sum`, four fields).
    Five concepts is right and twenty is two too many: the Lean concept is what pushed it over, and
    a later section that needs one should count it against the same budget rather than treating it
    as free.

- [x] **9. Separation Axioms** — `Separation.lean` · 5 concepts, 18 problems

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

  Flags: the diagonal-closed statement is `Topology.prod T T` and §7 has everything it needs —
  `Topology.continuous_mk_left` and `.continuous_mk_right` for the slices,
  `Topology.continuous_prod_mk` for the diagonal map itself, and `Topology.isOpen_prod_box` for
  the separating box. A subspace of a T_n space is T_n through
  `Topology.continuous_into_subspace` and `Topology.isClosed_subspace_iff`; do not reopen the
  subspace topology to prove anything about its closed sets.
  Each axiom is also a topological invariant, and §6 built the machine for saying so —
  `Homeomorphism.isOpen_iff` with `Homeomorphism.preimage_preimage` beside it. If a problem here
  wants "a space homeomorphic to a Hausdorff space is Hausdorff", it is those two and a transport
  of points, in the shape of `Homeomorphic.isCodiscrete`; do not restate them.
  `separation_closures` is stated in §4's vocabulary throughout — `T.mem_closure_iff` is
  the tool for all three, and "points are closed" is `T.isClosed_iff_closure_eq` at a singleton.
  "every metric space is normal" wants the distance from a point to a set, an infimum over
  a set of reals. It is available (`sInf`, with the definition marked `noncomputable`, which the
  extractor accepts) but it costs a concept of its own; leave it out unless the section is short.
  Urysohn's lemma is out of scope — see the last section below.
  §8 paid for the source's own counterexample, the **line with two origins**: it is
  `line.toTopology.sum line.toTopology` quotiented by the relation identifying the two copies of
  each point except the origin, which is a setoid of the same shape as `collapse` and the only
  thing the example still owes. Every neighbourhood of one origin then meets every neighbourhood
  of the other, so the space is T₁ and not Hausdorff, which no example now in the subject
  separates. Take it if `separation_examples` wants a fifth; `Topology.quotient`,
  `Topology.sum` and `Topology.continuous_inl` are all in hand.
  Two more things §8 leaves here. `unitInterval` and `unitInterval_closed` exist, so an example
  wanting a closed subset of the line need not build one. And a quotient of a T_n space is in
  general not T_n — which is why `separation_hereditary` is stated for subspaces and products and
  not for quotients; say so in prose rather than proving it, since the counterexample is
  `ℝ/ℚ` and that wants the Archimedean argument for its own sake.

  As built, and what it settled:

  - The **`@goal` moved** from §8's `quotient_examples` to `regular_normal`.
  - **The names are `Topology.IsT0`, `Topology.IsT1`, `Topology.IsHausdorff`, `Topology.IsRegular`
    and `Topology.IsNormal`** — the numbers where mathematics has no other name for the condition,
    the words where it has. **T₃ and T₄ carry `T.IsT1` as a conjunct**, which is the source's
    convention and is what makes the hierarchy a chain: without it a regular space need not be
    Hausdorff, and `Topology.isHausdorff_of_isRegular` could not be stated. A later section that
    wants the weaker, T₁-free "regular" should say so in its own name rather than change this one.
  - **The five definitions are checked by `Iff.rfl`**, so — as §7 found for `Topology.prod` — the
    order of the conjuncts is part of the answer, and each description names the order. Compiled
    against the variants a student will actually write (`¬ (y ∈ U)` for `y ∉ U`, `∀ (x : X) (y : X)`
    for `∀ x y : X`, renamed bound sets) the spec accepts them all, and it still rejects a
    definition missing a conjunct.
  - **Three of the section's flags were wrong about the route, in the same direction.** The
    diagonal statement wanted neither `Topology.continuous_prod_mk` nor the slices: it is
    `Topology.prod`'s own definition read twice, because a box around a point off the diagonal
    *is* the separating pair. The subspace statements wanted neither
    `Topology.continuous_into_subspace` nor `Topology.isClosed_subspace_iff`: the trace of an
    open set is open by `⟨U, hU, rfl⟩`, and that is five lines for each of the three axioms.
    And "points are closed" did not want `T.isClosed_iff_closure_eq` at a singleton; it is
    `Topology.isOpen_iff_nbhd` on `{x}ᶜ`, which is where the axiom's hypothesis already lives.
    The pattern, for the sections below: reach for a construction's **definition** before its
    universal property when what is being proved is a statement about its open sets.
  - **`Topology.mem_closure_singleton` and `Topology.closure_singleton_subset_iff` were not in
    the plan and are in the section.** They say that `x ∈ T.closure {y}` is "every open set
    containing `x` contains `y`", and that the same condition compares the two closures — the
    specialisation order, without the name. The T₀ characterisation is four lines on top of them
    and would not have fit in fifteen without them. §11's `sequential_closure` and §13's
    recognition arguments should look here first.
  - **`Metric.dist_pos` is new**, and it is the first line of every separation argument in a
    metric space. It was split out because `Metric.isHausdorff` runs to twelve lines with it and
    past fifteen without.
  - **A metric space is regular without the distance from a point to a set.** The flag budgeted a
    concept for `sInf`; what the proof needs is only the union of the balls of radius `ε / 2` about
    the points of the closed set, which is open by `Metric.isOpenSet_sUnion` and covers the set by
    `Metric.mem_ball_self`. Fourteen lines, no infimum, nothing `noncomputable`. **Normality is
    still not free**, though: two closed sets need a radius chosen at each point of each of them
    and the two compared, and that is where the infimum comes back — so "every metric space is
    normal" remains a section's decision, not a corollary of this one.
  - **The line with two origins was not needed.** `separation_examples` came to five problems
    without it — the metric, the codiscrete, the Sierpiński and the cofinite spaces already
    separate the three conditions pairwise — so §8's construction is still unspent and §10 or a
    later section may have it.
  - **`Homeomorphic.isHausdorff` is the shape to copy.** Transporting an axiom is `obtain ⟨e⟩`,
    the two sets pulled back along `e.invFun` (open by `e.continuous_invFun`), and `e.right_inv`
    to see that the two pulled-back points are still distinct. It needs neither
    `Homeomorphism.isOpen_iff` nor `.preimage_preimage`, which the flag named; a property stated
    with *points* as well as open sets moves along the map, not along the open-set equivalence.
    §10's connectedness and §12's compactness are stated without points and should use the flag's
    pair instead.
  - **No new import, and no deprecated name.** The fence is the same ten modules
    §7 left. One correction to add to the deprecation list below: **`push_neg` is deprecated in
    this toolchain** and prints the replacement it wants, so a proof that negates a hypothesis
    writes `push Not at h`. `t0_iff_closures` is the only proof here that needs it.
  - **Eighteen problems, 5 concepts, 584 lines**, with the longest proof at fourteen
    (`Topology.isT0_iff_closure_injective`, which was over before its two helpers were split out,
    and `Metric.isRegular`). The band holds.

---

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
  §8 makes the source's own phrasing sayable — a space is connected when it is not homeomorphic
  to a sum of two nonempty spaces — but do not define connectedness that way: the clopen form is
  what every proof here uses, and `Topology.sum` would drag a homeomorphism into each of them.
  If the equivalence is wanted, it is one problem at the end, with `Topology.continuous_sum_iff`
  for the two maps.

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
  so the section inherits the ball form and owes only the sequence. "Limits are unique exactly
  when the space is Hausdorff" is stated at §9's `Topology.IsHausdorff`, and the metric half is
  `Metric.isHausdorff` with `Metric.dist_pos`; none of the three is to be restated. The reverse halves of
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
  `unitInterval` is defined and `unitInterval_closed` is proved, in §8; `interval_compact` should
  be stated at that set rather than introducing an interval of its own.

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

  Flags: the vocabulary is §9's and is not to be rebuilt — `Topology.IsHausdorff` and
  `Topology.IsNormal` (which carries `T.IsT1` as its first conjunct, so `compact_normal` owes that
  conjunct too), `Topology.isT1_iff_isClosed_singleton` for "a point is a closed set", and
  `Topology.isHausdorff_of_isClosed_diagonal` where a diagonal argument is shorter than a pair of
  points.
  `compact_to_hausdorff`'s second half — a continuous bijection between them is a
  homeomorphism — is the closed-map form of §6's `Homeomorphism.ofOpenMap`, which §6 deliberately
  did not build: it is that definition with `Set.preimage_compl` in the middle, and it belongs
  here, where the hypothesis that makes the map closed lives. Present the bijection as §6 does,
  by the map that undoes it.
  `heine_borel` is `interval_compact` plus `compact_basics` plus `compact_metric`, so it
  is cheap *if* §12 landed. The plane case is paid for: §7's `plane_homeomorphic_product` and
  `taxicab_homeomorphic_product` identify both planes with `line.toTopology.prod line.toTopology`,
  and `ball_supNorm_eq_box` turns a supremum ball into a box wherever the argument wants one.
  §8 makes the source's other compact-Hausdorff result sayable: a continuous surjection from a
  compact space to a Hausdorff one exhibits the target's topology as the quotient topology, which
  is the equation `S = T.coinduced f` and is proved by `Topology.eq_of_isOpen_iff` once the map
  is known closed. `IsSaturated` and `Topology.isOpen_image_of_saturated` are the closed-set form
  of the recognition; take them if `compact_to_hausdorff` wants a third problem, and skip them
  otherwise — nothing else in the roadmap needs saturation.

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
is the one thing that is not. Neither §5 nor §6 needed an addition; §7 added
`Mathlib.Data.Set.Prod`, which is the only movement since §4, and the subject's fence is now the
ten modules `polya extract` reports. §8 added nothing either, which is the more surprising of the
two: `Setoid`, `Quotient` with its four operations, `Sum` with `Sum.elim` and `Sum.inl_injective`,
and `Set.preimage_image_eq` beside `Set.preimage_inr_image_inl` are all reachable under what §7
left, so `Mathlib.Data.Sum.Basic` was tested, found clean, and not needed. §9 added nothing
either, so the fence has stood still for three sections: `Set.infinite_univ`,
`Set.finite_singleton` and `Subtype.ext` are all under what §7 left. Test any further import
before adding it; the command is in `STYLE.md`, and the message to grep for is
`unknownIdentifier`, which Lean capitalizes.

`Mathlib.Data.Real.Archimedean` is **deprecated** in this toolchain and emits a warning naming
its replacement. Warnings are errors under publish, so import
`Mathlib.Algebra.Order.Archimedean.Real.Basic` instead. Two more names that look innocent are
deprecated the same way: `Set.diff_eq_empty` and `Set.diff_self`, whose replacements are
`Set.sdiff_eq_empty` and `Set.sdiff_self`. A **tactic** is deprecated the same way and
costs a publish as surely as a name does: `push_neg` prints a warning naming `push Not`, so a
proof that needs to negate a hypothesis writes `push Not at h` (§9's `t0_iff_closures`).

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
- `Topology.continuous_into_subspace`, `Topology.continuous_toSubspace`,
  `Topology.isClosed_subspace_iff`
- `Topology.induced`, `Topology.subspace_eq_induced`, `Topology.continuous_induced`,
  `Topology.induced_coarsest`, `Topology.eq_of_isOpen_iff`, `Topology.induced_induced`
- `Topology.prod`, `Topology.isOpen_prod_box`, `Topology.prod_eq_sUnion_boxes`,
  `Topology.continuous_fst`, `Topology.continuous_snd`, `Topology.isOpenMap_fst`,
  `Topology.isOpenMap_snd`, `Topology.continuous_prod_mk`, `Topology.continuous_prod_iff`,
  `Topology.continuous_mk_left`, `Topology.continuous_mk_right`
- `ball_supNorm_eq_box`, `isOpen_prod_of_isOpenSet_supNorm`, `isOpenSet_supNorm_of_isOpen_prod`,
  `supNorm_prod_homeomorphism`, `plane_homeomorphic_product`, `taxicab_homeomorphic_product`
- `preimage_sUnion_image`, `Topology.coinduced`, `Topology.continuous_coinduced`,
  `Topology.coinduced_finest`, `Topology.continuous_out_of_coinduced`, `coinduced_discrete`
- `kernelSetoid`, `quotient_mk_surjective`, `quotient_mk_eq_iff`, `kernelLift`,
  `kernelLift_injective`
- `Topology.quotient`, `Topology.continuous_mk`, `Topology.continuous_quotient_lift`,
  `IsSaturated`, `isSaturated_preimage`, `Topology.isOpen_image_of_saturated`, `quotient_discrete`
- `Topology.sum`, `Topology.continuous_inl`, `Topology.continuous_inr`, `Topology.isOpenMap_inl`,
  `Topology.isOpenMap_inr`, `Topology.continuous_sum_elim`, `Topology.continuous_sum_iff`
- `collapse`, `collapse_preimage_class`, `unitInterval`, `unitInterval_closed`,
  `collapse_point_isClosed`, `line_collapse_interval`
- `Topology.IsT0`, `Topology.IsT1`, `Topology.IsHausdorff`, `Topology.IsRegular`,
  `Topology.IsNormal`, `Topology.isT0_of_isT1`, `Topology.isT1_of_isHausdorff`,
  `Topology.isRegular_of_isNormal`, `Topology.isHausdorff_of_isRegular`
- `Metric.dist_pos`, `Metric.isHausdorff`, `Metric.isRegular`, `codiscrete_not_isT0`,
  `sierpinski_isT0`, `sierpinski_not_isT1`, `cofinite_isT1`, `cofinite_not_isHausdorff`,
  `discrete_isNormal`
- `Topology.mem_closure_singleton`, `Topology.closure_singleton_subset_iff`,
  `Topology.isT1_iff_isClosed_singleton`, `Topology.isT0_iff_closure_injective`, `diagonal`,
  `Topology.isClosed_diagonal_of_isHausdorff`, `Topology.isHausdorff_of_isClosed_diagonal`
- `Topology.isT0_subspace`, `Topology.isT1_subspace`, `Topology.isHausdorff_subspace`,
  `Topology.isHausdorff_prod`, `Homeomorphic.isHausdorff`

Two in particular: §7's `Topology.induced` is the shape `Topology.subspace` already had
(`∃ U, T.IsOpen U ∧ V = f ⁻¹' U`), so the subspace topology is a *case* of it and
`Topology.subspace_eq_induced` is `rfl`; and §4's `interior_boundary` builds on §2's
`union_of_opens_inside`, which is the statement that an open set is its own interior.

A third, from §8: `Topology.quotient` **is** `Topology.coinduced` at `Quotient.mk`, defined as
exactly that, so every theorem about the coinduced topology holds of a quotient with nothing
restated. A later section wanting a property of quotients should look for it on `coinduced`
first, and state it there unless it is about the class map in particular.

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

§8 wrote its citations in full from the start — `Topology.continuous_coinduced T (Quotient.mk s)`
in `Topology.continuous_mk`, `Topology.empty T'` in `Topology.isOpenMap_inl`,
`Metric.mem_ball line` in `unitInterval_closed` — and nothing stalled. The rule costs nothing when
it is followed first; follow it in every section from here. §9 did the same throughout —
`(Topology.mem_closure_iff T).mp`, `Metric.isOpenSet_ball M x _`, `rw [Metric.mem_ball M]` — and
nothing stalled there either. Structure *fields* stay in dot form (`M.dist`, `M.triangle`,
`M.symm`, `T.IsOpen`, `e.continuous_invFun`), since they arrive with the structure.

### Shapes that cost more than they look

- **Generating a topology from a family.** Avoid it — see §7. Every construction in §7 and §8 is
  defined directly instead, and each is a short `where`-bodied definition of the same shape as
  `Metric.toTopology`.
- **Subsets versus subspaces.** Compactness and connectedness are each stated twice in the
  literature — of a space, and of a subset. Define the subset version with opens of the ambient
  space, prove once that it agrees with the subspace being compact or connected, and never juggle
  subtypes again.
- **Quotients.** This bullet is struck. `Quotient.lift` was not where §8 stalled — nothing was.
  The four names `Quotient.inductionOn`, `.sound`, `.exact` and `.lift` carry every statement
  about a quotient, the setoid rides as an explicit argument like a `Metric`, and no proof ever
  chose a representative. Prefer `Quotient` to `Quot` and the obligations are the relation itself.
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
- **A definition beats its universal property, for a statement about open sets.** §9 planned three
  proofs around `Topology.continuous_prod_mk`, `Topology.continuous_into_subspace` and
  `Topology.isClosed_subspace_iff`, and all three came out shorter by reading `Topology.prod` and
  `Topology.subspace` directly — a box *is* a separating pair, and the trace of an open set is
  open by `⟨U, hU, rfl⟩`. The universal property is the tool when a **map** is being built or
  tested; the definition is the tool when an **open set** is being produced.

### The expensive proofs

In the order they arise, these are the ones to budget for and to split into helper problems:
§10's connectedness of an interval; §11's two reverse halves, which pick a point from each of a
shrinking sequence of balls; and, far above the rest, §12's compactness of a closed interval.

§5's bridge between ε-δ and open sets was on this list and is struck from it: built, it is ten
lines and wanted no helper, because §1's balls and §2's `Metric.toTopology` had already made the
two sides the same data. §7's identification of the plane with a product was billed as a capstone
and came out at three short problems, for the same reason. Take the remaining three as estimates
of the same kind — a proof looks expensive until the definitions line up, and the way to find out
is to write the statement and see what the earlier sections hand over.
