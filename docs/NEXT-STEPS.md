# P29 continuation and actual attempts

None of the ten principal new results and listed corollaries is complete. Do not promote any support theorem to path-minimality.

## Actual work
- Full latest v1 PDF/TeX, AppendixA, author list and bibliography read; all new theorem/corollary numbers and source binders recorded in SOURCE-AND-SEMANTICS.md. Recalled companion-paper results are proof obligations, not extra hypotheses.
- Searched local mathlib graph filenames and declaration names, verified actual IncMatrix/LapMatrix/AdjMatrix/Hermitian Spectrum implementation and downstream APIs with Lean. Used genuine characteristic-polynomial roots with multiplicities and decreasing sort, not minimal-polynomial eigenvalue sets or arbitrary numeric sequences.
- Read TauCeti Schatten formal definitions and triangle/ideal proofs. They do not themselves provide the p=3 Clarkson–McCarthy source inequality or path-minimality theorem. They were not imported or claimed axiom-audited for P29.
- Queried QuanyuTang public repositories and pinned graph-p-energy-certificates @9ab79d5385f8c17579e4b6b51b31da92be4807da. Its tree has Sage scripts/logs, not Lean theorem modules; read the line-graph script fully. Public web discovery returned no usable formal path-minimality proof; this is not a claim none exists.
- Proved actual signless D+A incidence Gram identity and PSD; actual adjacency closed-walk trace and symmetric matrix trace-power eigenvalue sum. Actual positive-energy filter and odd integer half-total bound were proved with no trace assumption.
- Turned Appendix local moments into actual finite matrix identities. Direct fifth-power simplification failed; repaired with five verified matvec steps for each L=2,…,6. Defined actual finite simple local graphs, verified their degrees using kernel `decide`, and proved each matrix is the actual signless Laplacian plus its rank-one update.
- Reconstructed six exact rational Bernstein certificates using standard-library Fraction/binomial arithmetic; every identity, coefficient nonnegativity and source-form equivalence is checked in Lean by ring/norm_num. Python/Sage calculations are not trusted axioms. No native_decide or new axioms.
- Proved shifted q polynomial, ratio factorization, rational margin and actual fifth-order scalar lower bound. These do not prove actual graph spectral-shift moments or the infinite local stability family.

## Missing chain
1. Companion arXiv:2605.22730v3 full total-energy/path rigidity and bipartite stoploss/third-order-convex comparison, including its deletion, splicing, singular value spectral shifts, path/cycle mode formulas and moment/envelope arguments.
2. Actual bipartite adjacency ± spectral multiset symmetry, exact path spectrum and positive energy; graph isomorphism invariance and connected path attainment; source Theorems3.2/3.3. The odd half-total substep is complete, but the path comparison is not.
3. Clarkson–McCarthy Schatten p=3 for actual Hermitian blocks, star spectrum, positive-energy vertex addition and real exponent upgrade; connected-component spectral additivity and cycle-vertex component count; strict p=4 path deficit and full induction (Theorem3.6).
4. Actual edge-index unsigned incidence (mathlib currently includes zero nonedge columns), subdivision graph connectedness/path isomorphism, AB/BA nonzero spectral multiset equality including zeros; signless/Laplacian bipartite similarity, Loewner eigenvalue monotonicity and source admissibility/AC/a.e.-derivative semantics; Theorem3.7 and Corollaries3.8/3.10/3.11/3.13.
5. Actual rank-one trace differentiation/functional positive parts and Jensen, spectral interval measure and packing, moment stability for arbitrary path/local lengths; integrate the verified scalar certificates with actual moments to prove Lemmas3.14/3.15.
6. Cycle terminal comparison and weak majorization, exact sine/cosine path/cycle spectrum; structural deletion-minimal counterexample/bridge/disjoint-union argument; Theorem3.17.
7. Actual line graph connectedness/path isomorphism and NᵀN=2I+A(line graph), shift relation with full multiplicity; stoploss integral→real p-energy; Theorem3.18 and sharpness.
8. Full exact-source semantic audit and clean/checker/Comparator/same-final-commit green Actions only after all principal exports are actually proved. No Palomar submission without a separate user request.

Read actual modules and logs when resuming, not only this status note. Dependency caches in development are read-only; publicly pinned Git source is the reproducibility contract. Keep incomplete repositories without workflows and with Actions disabled.
