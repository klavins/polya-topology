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

## Binders

Bind a variable implicitly wherever that makes the proofs downstream read better, and the call
sites decide it, not taste. A fact used **backwards** — rewritten into a goal, matched against
one by `exact`, `apply` or `simp`, or having `.mp`/`.mpr` taken — has its variables fixed by the
statement it lands in, so naming them is noise. A fact used **forwards** — instantiated into a
`have` for `linarith`, or applied to a chosen witness — has to be given its arguments, and
implicit binders would force `@` or a type ascription instead.

The test is mechanical: look at every use in the subject, and if none of them passes the
argument, make it implicit. Here that put the line between

```
implicit   Metric.symm  Metric.eq_zero  Metric.dist_self  Metric.mem_ball
           Metric.ball_mono (the centre)  Norm.eq_zero  Norm.mem_ball_zero
explicit   Metric.triangle x y x   Norm.smul (-1) v   Norm.triangle v (-v)
           Norm.neg (v - w)   Metric.ball_subset_ball x y δ   Metric.nonneg x y
```

Everything on the first line is only ever written bare; everything on the second chooses one of
its arguments — the detour of a triangle inequality, the scalar of a scaling, the instance to
rewrite backwards — and implicit binders there cost more than they save. A declaration nothing
uses yet keeps explicit binders until something does.

For a structure's fields this matters most, since the reference is the context every later
problem compiles against. Say in the description which fields are implicit, or every student
guesses. Construction uses named binders — `symm {x y} := abs_sub_comm x y` — because a bare
`eq_zero := by rw [...]` never introduces the implicit points and the rewrite fails on a goal
still under its binders.

## Specs

A spec must accept every *correct* encoding, not just the reference's. A student who binds the
points explicitly, or who writes non-degeneracy as `x = y ↔ dist x y = 0`, has not made a
mistake, and a spec that rejects them is the spec's bug. Two tactics do the work:
`by apply M.symm` accepts either binder style, and `by simp [M.eq_zero]` accepts an `↔` either
way round and either binder style with it. Do not use `first | exact … | exact …` — the unused
branches raise `linter.unusedTactic`, and warnings become errors under publish. Before
publishing a structure, compile its spec against variants of every field shape plus one wrong
definition, which must still fail.

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

## Prose

A **concept description is at most 400 characters** — about seven lines at the width the
problem page gives it. It sits in the left column beside the problem, so every line it spends
is a line the student does not have for the mathematics they are working on.

What belongs in it: what the concept is, in a sentence, and **why the subject needs it**. What
does not: anything a problem already says, any worked example, any Lean, any forward reference
to a later problem. The concept column is read before and beside the problems, not instead of
them.

`plane_norms` was 848 characters — it carried the whole `p`-norm family, the unit balls, and the
punchline about equivalent metrics. The family is exposition, so it went to `define_sup_norm`,
the problem that needs it; the unit balls were already in the two problems that build them. What
is left is 326 characters saying what the concept is for: two lengths on one set, and the
question of what a metric keeps.


A problem's `@preamble` and `@description` together get **about 22 lines of 55 characters** —
17 to 27. That is the room the problem page has; anything past it is pushed out of sight. The
skill's `reference/style.md` carries the command that counts them over a bundle, and no problem
here is over.

Write only what a student needs in order to start *this* problem. The cuts that bought the most
room, and that are the ones to look for first:

- **Forward references.** "It need not be asked, because it follows, as a problem below will
  show" — the student cannot use this, and the problem that proves it makes the point itself,
  where it is earned.
- **Morals about method.** "One asks of a definition only what cannot be deduced." True, and
  not what the reader is here for.
- **A second telling of the concept.** The concept description is already on the page, beside
  the diagram.
- **Lean mechanics met before.** How a structure instance is written belongs in `define_line`,
  once, not in every definition that follows.

What is worth keeping but is not needed to start *this* problem goes in the preamble of the
problem that does need it — not in the concept description, which has the tighter budget above
and carries no exposition at all. The survey of the `p`-norm family has been in both places and
belongs in neither but one: it is exposition for the supremum norm, so it sits in
`define_sup_norm`, trimmed to the four lines that problem can spare.

A problem whose prose is honestly over the budget is two problems.

## Sources

The subjects follow published treatments for their selection and order of results, and name them
in `@reference` lines. The prose, the Lean and the problems are written here: a source supplies
the syllabus, never the sentences. Subjects carry CC BY-SA 4.0, and the text of it is the
`LICENSE` file in each subject's directory.
