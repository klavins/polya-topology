# Polya Topology

A Polya content repository for topology. Its subjects are built from the ground up: metric
spaces first, then the open sets they generate, and then the spaces that have open sets without
having distances. The plan is that it should eventually hold a full course in the subject; today
it holds the first eight sections of one. `ROADMAP.md` says what the rest is to be.

| subject | what is in it |
|---|---|
| `generaltopology` | **Metric Spaces** — the axioms and what follows from them, open and closed balls and spheres, bounded sets, normed vector spaces, the metric a norm induces, and two norms on the plane. **Topological Spaces** — the sets a metric calls open, those properties taken as a definition, closed sets and neighbourhoods. **Basic Examples** — the discrete, codiscrete, Sierpiński, cofinite and subspace topologies. **Closure, Interior and Boundary** — the smallest closed set around a set and the largest open set inside it, the points of a closure, the boundary, and dense sets. **Continuous Functions** — the ε-δ definition, continuity as openness of preimages, the theorem that the two agree, and the definition tested on the example spaces. **Homeomorphisms** — when two spaces are the same space, open and closed maps, equivalent metrics and the plane measured two ways, and the invariants that tell the three topologies on a two-point set apart. **Subspaces and Products** — what maps a subspace admits, the topology induced along any map, the product of two spaces and the maps into and out of it, and the plane shown to be the product of two lines. **Quotients and Sums** — the final topology along a map out of a space, quotients in Lean, the quotient space with its saturated sets, the disjoint union of two spaces, and a subset collapsed to a point. 142 problems over 40 concepts. |

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
