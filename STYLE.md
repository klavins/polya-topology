# Style for PolyaTopology subjects

The house rules are the `polya-author` skill's; this file records what is particular to this
repository, and it wins where the two differ.

## The fence, and why it is thin

A section's imports are the whole of the library a student may use. In this repository they
exclude **Mathlib's `Mathlib.Topology.*` and everything that reaches it**. That is the point of
the repository: a student builds metric spaces, open sets, continuity and compactness, and a
fence that already contains `MetricSpace`, `Metric.ball`, `IsOpen` or `Continuous` turns every
problem into a search for the Mathlib name that closes it.

The fence of `GeneralTopology/MetricSpaces.lean` is

```lean
import Mathlib.Data.Real.Basic      -- ℝ, its order and its field structure
import Mathlib.Data.Set.Basic       -- Set, {y | p y}, ⊆, ∪, ext
import Mathlib.Algebra.Module.Prod  -- AddCommGroup and Module ℝ, on a type and on a product
import Mathlib.Tactic.Linarith      -- linarith, and norm_num beneath it
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
```

Before adding an import, compile a file that imports it and asks for `MetricSpace`, `IsOpen`,
`TopologicalSpace` and `Continuous`. All four must be unknown identifiers. Several innocuous
modules fail this: anything under `Mathlib.Analysis.*`, and in particular **`Real.sqrt`**, whose
home module imports `Mathlib.Topology.Instances.NNReal.Lemmas`, since the square root is built
as the inverse of a monotone map and needs order-topology machinery to exist.

## No square roots

The consequence of the paragraph above is that the Euclidean length of a vector — the square
root of a sum of squares — cannot be written in this repository, and neither can any `p`-norm
for `1 < p < ∞`. Do not import a square root to get one; choose an example that teaches the
same thing without one. The two ends of the `p`-norm family, `p = 1` and `p = ∞`, are rational
in the coordinates and carry the lesson that the middle of the family would: they are different
functions, their unit balls are different sets, and each one's balls fit inside the other's.
Where a reader would expect the Euclidean norm, say in the prose that it needs a root and that
the root is not available here — do not pretend the family has only two members.

## The plane is `ℝ × ℝ`

Not `Fin n → ℝ`. A point is a pair, its coordinates are `v.1` and `v.2`, addition and scaling
act coordinatewise by definition, and `Prod.ext` proves two pairs equal. `Finset.sum` and
`Finset.sup'` would put more Lean apparatus than topology into every proof.

## Bundling, not classes

A metric is a `structure Metric (X : Type u)` and a norm a `structure Norm (V : Type u)`, each
carried as an ordinary argument: `M.dist x y`, `N.norm v`. They are not classes and there are no
instances. A student reads `M.triangle x y z` as the hypothesis it is, and an exercise can never
be closed by an instance the student did not know was in scope.

Because a structure's generated shape check is nearly vacuous — any structure of the right arity
passes — **every structure definition problem carries a `/-- @spec -/` naming its fields**, and
so does every `where`-bodied `def`, which has no single body to compare and is an extraction
ERROR without one.

## Proofs

No proof runs past fifteen lines. When one would, the way out is a lemma of its own, given its
own problem and taught before the problem that needs it: `eq_zero_of_abs_le_zero`,
`prod_eq_zero` and `max_add_max` all exist for that reason, and each is a small true thing worth
knowing. A structure definition counts as one proof per field, and the whole definition should
still fit on a screen.

Reference proofs are the proof a student should write: tactic style, one step per line, `show`
where a membership or a distance has to be restated as what it abbreviates, `have h : … := hy`
to name a hypothesis that is already the thing wanted, and `linarith` for the arithmetic at the
end. Automation closes a goal; it does not replace the argument.

## Sources

The subjects follow published treatments for their selection and order of results, and name them
in `@reference` lines. The prose, the Lean and the problems are written here: a source supplies
the syllabus, never the sentences. Subjects carry CC BY-SA 4.0, and the text of it is the
`LICENSE` file in each subject's directory.
