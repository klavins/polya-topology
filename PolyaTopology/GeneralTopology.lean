import PolyaTopology.GeneralTopology.MetricSpaces

/-! @subject generaltopology
@title General Topology
@author Eric Klavins
@license CC-BY-SA-4.0
@reference Urs Schreiber, Introduction to Topology 1 — Point-set Topology, nLab: https://ncatlab.org/nlab/show/Introduction+to+Topology+--+1 — this subject follows its selection and order of results; the prose, the Lean, and the problems are written here.
@reference The nLab: https://ncatlab.org
Topology is the study of nearness without measurement: of which points lie close to which, asked without any account of how close. The subject begins one step before that, with measurement itself. A metric space is a set together with a rule assigning a distance to each pair of its points, and nearly every space a working mathematician meets carries such a rule. From the distances one reads off the balls, from the balls the open sets, and from the open sets the topology. By the end of that passage the distances have been forgotten and only the nearness remains.

The first section builds the beginning of it. We define a metric space, deduce from its axioms the two facts the axioms did not ask for, and construct the open balls, the closed balls and the spheres. We say what it means for a set to be bounded, and prove that boundedness survives taking subsets and unions. We then treat the source of most metrics in practice: a norm on a real vector space, which measures the length of a vector and so the distance between two of them. The section ends on the plane, where two different norms — the one that adds the magnitudes of the coordinates and the one that takes the larger of them — have visibly different unit balls, a diamond and a square, and yet each one's balls fit inside the other's. That is the first sign that a topology remembers less than a metric does.

Mathlib's own metric spaces and topological spaces are not imported, and no problem may appeal to them. Everything is built from the real numbers, sets, and the language of real vector spaces, so that a student who finishes the section has the apparatus rather than a borrowed name for it. One consequence is visible in the choice of examples: the Euclidean length of a vector in the plane requires a square root, which is beyond what this fence holds, so the plane is measured here by two lengths that need no roots at all.
-/
