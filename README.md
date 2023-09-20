# Projective space

This project contains:
- The definition of a smooth manifold structure on the projective space of a normed k-vector space E, if k is a complete nontrivially normed field and continous linear forms separate points on E. Any closed hyperplane of E can serve as model. To put the ChartedSpace instance on the projective space, we need to choose a model so we also require a Nonempty instance on  {u : E // u \ne 0} so we can pick a nonzero continous linear form.
- Some tools to prove smoothness of maps to/from projective space:
  - The quotient map from E-{0} to projective space is smooth;
  - A map from projective space to a smooth manifold is smooth if its composition with the quotient map E-{0} -> P(E) is smooth;
  - More generally, a map N x P(E) -> M is smooth if its composition with (id, quotient map) : N x E-{0} -> N x P(E) is smooth.
- Using these tools, we give examples of smooth maps:
  - If E is a finite-dimensional euclidian space, we prove that the map from the sphere to P(E) is smooth;
  - In general, we define the action of GL(E) on P(E) and prove that the action map GL(E) x P(E) -> P(E) is smooth.
     
