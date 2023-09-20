# Projective space

This project contains:
- The definition of a smooth manifold structure on the projective space of a normed k-vector space E, if k is a complete nontrivially normed field and continous linear forms separate points on E. Any closed hyperplane of E can serve as model. To put the ChartedSpace instance on the projective space, we need to choose a model so we also require a Nonempty instance on  {u : E // u \ne 0} so we can pick a nonzero continous linear form.
- Some tools to prove smoothness of maps to/from projective space:
  - The quotient map from E-{0} to projective space is smooth;
  - A map from projective space to a smooth manifold is smooth if its composition with the quotient map E-{0} -> P(E) is smooth;
  - More generally, a map N x P(E) -> M is smooth if its composition with (id, quotient map) : N x E-{0} -> N x P(E) is smooth.
- Using these tools, we give examples of smooth maps:
  - If E is a finite-dimensional euclidian space, we prove that the map from the sphere to P(E) is smooth;
  - In general, for E complete, we define the action of GL(E) on P(E) and prove that the action map GL(E) x P(E) -> P(E) is smooth.

TODO:
- I am having trouble with the Nonempty {u : E // u \ne 0} instance, I want to generate it automatically if we know that FiniteDimensional.finrank k E \geq 1 but I am getting "cannot find synthesization order for instance" errors.
- The smoothness results should be upgraded to ContMDiffOn results (maybe also ContMDiffAt ?).
- I have not proved that the action of GL(E) on P(E) is a group action.
- Segré and Veronese maps !

# Detail of the files

## ClosedHyperplanes.lean 

Preliminaries on closed hyperplanes in E, in particular the construction of a retraction on a closed hyperplane and an isomorphism between any two closed hyperplanes. Also contains the construction of a SeparatingDual instance if E is finite-dimensional.

## MapFromPhere.lean

If E is an euclidien space, construction of the map from the sphere and proof that it is smooth.

## playground.lean

For tests.

## ProjectiveSpaceGeneral.lean

- Manifold structure on E-{0}.
- Some general lemmas.
- Construction of the charts, proof that they are continuous, proof that change of charts is smooth.

## ProjectiveSpaceManifold.lean

- Choice of a model hyperplane.
- Charted space structure on projective space.
- Smooth manifold structure on projective space.

## SmoothMaps.lean

- The quotient map E-{0} -> P(E).
- Construction of local sections of the quotient map, and proof that they are smooth.
- A map P(E) -> M is smooth if its composition with the quotient map E-{0} -> P(E) is smooth.
- A map N x P(E) -> M is smooth if its composition with (id, quotient map) : N x E-{0} -> N x P(E) is smooth.
- If E is complete, construction of the action of GL(E) on P(E) and proof that it is smooth.
