import PolyaTopology.GeneralTopology.MetricSpaces
import PolyaTopology.GeneralTopology.TopologicalSpaces
import PolyaTopology.GeneralTopology.BasicExamples
import PolyaTopology.GeneralTopology.Closure

/-! @subject generaltopology
@title General Topology
@author Eric Klavins
@license CC-BY-SA-4.0
@reference Urs Schreiber, Introduction to Topology 1 — Point-set Topology, nLab: https://ncatlab.org/nlab/show/Introduction+to+Topology+--+1 — this subject follows its selection and order of results; the prose, the Lean, and the problems are written here.
@reference The nLab: https://ncatlab.org
Topology is the study of nearness without measurement: of which points lie close to which, asked without any account of how close. The subject begins one step before that, with measurement itself. A metric space is a set together with a rule assigning a distance to each pair of its points, and nearly every space a working mathematician meets carries such a rule. From the distances one reads off the balls, from the balls the open sets, and from the open sets the topology. By the end of that passage the distances have been forgotten and only the nearness remains.

**Metric Spaces** builds the beginning of it. We define a metric space, deduce from its axioms the two facts the axioms did not ask for, and construct the open balls, the closed balls and the spheres. We say what it means for a set to be bounded. We then treat the source of most metrics in practice: a norm on a real vector space, which measures the length of a vector and so the distance between two of them. The section ends on the plane, where two different norms — the one that adds the magnitudes of the coordinates and the one that takes the larger of them — have visibly different unit balls, a diamond and a square, and yet each one's balls fit inside the other's. That is the first sign that a topology remembers less than a metric does.

**Topological Spaces** makes the passage. We single out the sets a metric calls open, prove the three properties they have, and then take those three properties as a definition that needs no distance at all. Every metric space becomes a topological space; closed sets and neighbourhoods follow, and a set turns out to be open exactly when it is a neighbourhood of each of its own points — the form in which nearly every later statement is made.

**Basic Examples** stocks the subject. The two extremes that bound every topology on a set, the two-point space whose asymmetry is the source of most counterexamples, the topology whose open sets leave out only finitely many points, and the one a subset inherits from the space around it — the construction by which nearly every space one meets is built.

**Closure, Interior and Boundary** puts the apparatus to work on an arbitrary set. Every set sits inside a smallest closed set and around a largest open one; what lies between the two is its boundary, and it is empty exactly when the set is both open and closed. A point belongs to the closure exactly when the set is found arbitrarily near it, which in a metric space is a statement about balls. The section ends with the rationals, a countable set whose closure is the whole real line.

Mathlib's own metric spaces and topological spaces are not imported, and no problem may appeal to them. Everything is built from the real numbers, sets, and the language of real vector spaces, so that a student who finishes has the apparatus rather than a borrowed name for it. One consequence is visible in the choice of examples: the Euclidean length of a vector in the plane requires a square root, which is beyond what this fence holds, so the plane is measured here by two lengths that need no roots at all.
-/
