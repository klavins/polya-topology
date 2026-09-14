# Polya Topology

A Polya content repository for topology. Its subjects are built from the ground up: metric
spaces first, then the open sets they generate, and then the spaces that have open sets without
having distances. The plan is that it should eventually hold a full course in the subject; today
it holds the first thirteen sections of one. `ROADMAP.md` says what the rest is to be.

| subject | what is in it |
|---|---|
| `generaltopology` | **Metric Spaces** — the axioms and what follows from them, open and closed balls and spheres, bounded sets, normed vector spaces, the metric a norm induces, and two norms on the plane. **Topological Spaces** — the sets a metric calls open, those properties taken as a definition, closed sets and neighbourhoods. **Basic Examples** — the discrete, codiscrete, Sierpiński, cofinite and subspace topologies. **Closure, Interior and Boundary** — the smallest closed set around a set and the largest open set inside it, the points of a closure, the boundary, and dense sets. **Continuous Functions** — the ε-δ definition, continuity as openness of preimages, the theorem that the two agree, and the definition tested on the example spaces. **Homeomorphisms** — when two spaces are the same space, open and closed maps, equivalent metrics and the plane measured two ways, and the invariants that tell the three topologies on a two-point set apart. **Subspaces and Products** — what maps a subspace admits, the topology induced along any map, the product of two spaces and the maps into and out of it, and the plane shown to be the product of two lines. **Quotients and Sums** — the final topology along a map out of a space, quotients in Lean, the quotient space with its saturated sets, the disjoint union of two spaces, and a subset collapsed to a point. **Separation Axioms** — how well a topology tells its points apart: T₀, T₁ and Hausdorff, the example spaces that sit between them, each axiom read through closures, the constructions that keep them, and the regular and normal spaces above them. **Connectedness** — a space in one piece, connectedness of a set and of the space it inherits, the interval that does not fall apart, the intermediate value theorem, connected components, and paths. **Sequences and Convergence** — the limit of a sequence with balls and then with neighbourhoods, how many limits a space allows, the closure and closedness read off sequences, continuity tested one sequence at a time, and Cauchy sequences with the spaces that complete them. **Compactness** — open covers and finite subcovers, the finite sets and the codiscrete spaces that are compact and the infinite discrete spaces that are not, closed subsets of compact spaces, compact sets in a metric space as bounded and closed, the continuous image of a compact set, the extreme value theorem, and the unit interval. **Compact Hausdorff Spaces** — a compact set held apart from a point and so closed, the compact sets and the closed sets coinciding, closed maps and homeomorphisms out of a compact space, the quotient a continuous surjection exhibits, regularity and normality, the tube lemma with the product of two compact sets, and compact meaning closed and bounded on the line and in the plane. 236 problems over 65 concepts. |

The outline follows Urs Schreiber's *Introduction to Topology* on the
[nLab](https://ncatlab.org/nlab/show/Introduction+to+Topology), which supplies the selection and
order of the results and is gratefully acknowledged. The prose, the Lean and the problems are
written here. Subjects carry CC BY-SA 4.0; the text is the `LICENSE` file in each subject's
directory.

## The one rule that shapes everything

**Mathlib's topology is not imported.** In `generaltopology` the identifiers `MetricSpace`,
`Metric.ball`, `IsOpen`, `TopologicalSpace` and `Continuous` do not resolve, so no problem can be
closed by finding the Mathlib lemma that already knows the answer. A student defines the
apparatus and proves its properties from the real numbers, sets, and the language of real vector
spaces.

The rule has one visible consequence. `Real.sqrt` lives in a module that imports
`Mathlib.Topology.Instances.NNReal.Lemmas`, so it is outside the fence, and with it go the
Euclidean norm and every `p`-norm strictly between `1` and `∞`. The plane is therefore measured
here by the two ends of that family — the taxicab norm `|x| + |y|` and the supremum norm
`max |x| |y|` — whose unit balls are a diamond and a square, and which nonetheless cannot be told
apart by any statement of the form "some ball about `x` lies inside `S`". `STYLE.md` says how to
test a candidate import, and what to do instead of reaching for a root.

## Working on it

```bash
polya build generaltopology      # does the Lean compile?
polya extract generaltopology    # every problem checked against its own spec; writes bundles/
polya simulate generaltopology define_sup_norm   # a model plays the student on one problem
polya publish generaltopology    # to the instance named in .env
```

Read `STYLE.md` before writing content, and the `polya-author` skill for the house conventions:
https://github.com/klavins/MUPolya/tree/main/skills/polya-author

To install that skill for Claude Code, once:

```bash
git clone https://github.com/klavins/MUPolya ~/Code/MUPolya    # if you do not have it
mkdir -p ~/.claude/skills
ln -s ~/Code/MUPolya/skills/polya-author ~/.claude/skills/polya-author
```
