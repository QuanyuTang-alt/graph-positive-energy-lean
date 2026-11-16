# Errata and deviations

Pinned source arXiv:2606.30996v1. Use published theorem numbers and TeX labels from the PDF/TeX. No source erratum is asserted. Missing formal proofs and our own compilation repairs are not paper errors. Same-assistant checking only; no independent verifier.

Counts: 0 asserted errata, 3 deviations.

## Errata
None asserted. No principal theorem is claimed complete.

## Deviations
1. **Scope, Theorems3.2/3.3/3.6/3.7/3.17/3.18 and application corollaries.** Only complete foundations and finite certificate substeps ship; none of the path-minimality results is formally proved.
2. **Unsigned incidence.** [GraphMatrices](../GraphPositiveEnergy/GraphMatrices.lean) uses mathlib's columns indexed by all unordered pairs, with nonedges zero. The actual Gram equals signless D+A, but edge-only column restriction/nonzero spectral multiset and line-graph bridge are still required. This is not silently declared equivalent to all source spectral constructions.
3. **AppendixA certificate verification.** Finite local fifth moments and scalar envelopes are generated as exact Lean statements with explicit polynomial/rational vectors and verified by Lean's kernel through ring/norm_num/decide. The source Sage scripts are only read-only references, never proof dependencies. Arbitrary-length stability, actual spectral envelope consumption and graph deletion remain unproved. See [next steps](NEXT-STEPS.md).

The original adjacency positive p-energy is literally the full actual spectrum's positive-part sum for p>0; strict-positive filtered equivalence is proved. No p=0 convention, alternative eigenvalue set, assumed companion theorem or fake principal predicate is introduced.
