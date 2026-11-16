# P29 supporting-declaration semantic review

**Same-assistant review only.** This is not an independent review, a principal-theorem audit, or Palomar certification. Source: arXiv:2606.30996v1, full PDF/TeX read. The exact public code of all five implementation modules was reviewed; fingerprints are in verification/source-hashes.json. All ten new principal theorem/corollary targets remain unproved.

## Actual spectral/energy definition unit
`adjacencyEigenvalues` is mathlib's real decreasing finite spectrum of the genuine 0–1 adjacency matrix, not a chosen arbitrary sequence. `adjacencyEigenvalues_characterization` identifies its full list with the descending characteristic-polynomial roots. `adjacencyEigenvalues_card` and `adjacencyEigenvalues_antitone` preserve the number of vertices, zero modes and ordering. Imported finite-dimensional spectral-theorem sources were read: the sorted values are built from actual orthogonal eigenspaces; algebraic multiplicity and uniqueness of the sorted list follow from the characteristic-root characterization. This is not the set of minimal-polynomial roots, which would lose multiplicities.

`positiveEnergy` is the finite sum of max(λ,0)^p on the exact p>0 source carrier. Its proved filtered identity is the literal sum over λ>0; Real.zero_rpow uses p≠0, not a p=0 default. `totalEnergy` is the literal absolute-eigenvalue p-power sum. The proof of odd half-total reindexes the entire actual spectrum, invokes the proved trace-of-powers/closed-walk bridge and uses the exact scalar odd-power identity. No energy/path comparison or trace positivity is assumed.

DEFINITION BODY_MATCH: OK for these actual finite graph definitions.
PUBLIC_CARRIER: OK, finite simple graph and p>0; no off-domain fallback semantics.
WELL_DEFINEDNESS/CHARACTERIZATION: mathlib spectral construction plus proved characteristic-root characterization consumed; literal finite energy sums require no extra choices.
CHOICE_INDEPENDENCE: sorted characteristic-root list fixes the eigenvalue tuple independently of eigenvector-basis choices.
DEFINITION_VERDICT: PASS for supporting objects only; no principal path comparison follows.

## Binders of operator bridge results
| Declaration family | Expanded binder | Classification | Source meaning |
| --- | --- | --- | --- |
| Graph definitions/theorems | V, Fintype V, DecidableEq V | TYPING | finite vertex carrier / executable equality |
| Graph definitions/theorems | G, DecidableRel G.Adj | TYPING/SOURCE | actual finite simple graph and decidable adjacency |
| Incidence Gram/PSD | no analytic/spectral estimate input | none EXCESS | D+A factorization is proved from actual incidence |
| Walk/power trace | k:ℕ | SOURCE | exact length or matrix power |
| Hermitian trace power | actual M and hM:IsHermitian M | SOURCE | generic real symmetric matrix substep |
| Spectrum reindex | f:ℝ→ℝ | TYPING | finite sum reindexing, not convex comparison |
| Positive-energy filtered sum | p:ℝ, hp:0<p | SOURCE | source definition exponent carrier |
| Odd-energy half-total | k, Odd k, 0<k | SOURCE | natural odd positive exponent; embeds into ℝ |
| Exact local matrix/graph certificates | x:ℝ only | SOURCE/TYPING | scalar rank-one parameter in actual finite matrices; identities proved for all x |
| Scalar fifth-order lower bound | y≥0, y≤5, 3≤t≤4 | SOURCE | pointwise source window; not claimed to be supplied by a graph spectrum |
| Envelope nonnegativity | t and stated closed rational interval | SOURCE | exact six AppendixA interval predicates |

No companion/path-minimality, PSD, spectral shift, graph moment or convex comparison is hidden in a final support binder. EXCESS count for actual graph bridges: 0. These rows review supporting assertions; a passing five-bin audit of every principal theorem cannot exist because no principal Lean exports exist. Generic source-form scalar conditions must not be promoted to graph hypotheses.

## Literal incidence and local graph matrices
`signless` is D+A. `incidence_gram` proves the actual mathlib unsigned incidence matrix product equals D+A. Mathlib uses all unordered vertex pairs as columns; nonedges are zero. The edge-only/source subdivision and line-graph spectral multiset bridge are still outstanding, not asserted by this Gram result.

For each L=2,…,6, localGraphL is the actual finite simple path-plus-leaf graph with vertices u=1, a=0, internal vertices 2,…,L, and extra leaf L+1. The fromRel construction symmetrizes the listed edges and removes loops. Every degree is kernel-decided on the concrete finite graph. `localMatrix_graph_L` proves its matrix exactly equals signless(localGraphL)+x·bbᵀ, with the vector having ones at u/a. Thus these certificates are not merely unrelated numerical arrays. Five genuine matvec equalities per model are composed to prove the fifth moments. Actual arbitrary-length stability and graph embedding into a general H are not proved.

`localIter` vectors are explicit polynomial certificates, not provisional mathematical objects or assumed witnesses. `envelopeCoeffs` and `envelopePoly` are literal rational arrays/polynomials. Six checked source-form identities relate the expanded polynomials to the AppendixA expressions with Astar/Bstar/Kstar. Six checked Bernstein decompositions and coefficient nonnegativity prove the closed-interval inequalities. The generator's rational arithmetic is not a trust boundary: all claims are checked by Lean's kernel. Statements could not be accepted merely because Python prints PASS.

## Verified scope and remaining audit boundary
76 supporting theorems, 60 definitions, 136 explicit axiom targets. Only the three standard axioms appear; no new axioms, unfinished holes or native evaluation certificates. Regeneration preserves current Lean files; development cache use is not isolated clean acceptance. No actual full path-minimality theorem, companion lemma, minmax/Loewner spectral comparison, infinite stability, full line-graph shifted spectrum, deletion counterexample or real-p threshold integration is certified. No Comparator or Actions success is claimed. Detailed open obligations appear in NEXT-STEPS.md.
