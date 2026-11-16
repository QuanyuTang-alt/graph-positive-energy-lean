# P29 exact latest source and target inventory

Latest checked release **arXiv:2606.30996v1**: live submission history contains v1 only, unversioned PDF agrees (24 pages). Full 2367-line TeX manuscript including appendix and bibliography read. Internal filename applications_arxiv_v1.tex is not used to select version. Original authors in order **Yinchen Liu, Quanyu Tang**.

All graphs are finite, simple, undirected, unweighted; connected graph has n≥1 vertices. Eigenvalues are actual adjacency/Laplacian/signless matrices, with full algebraic multiplicity. Matrix eigenvalues are listed nonincreasingly. Positive adjacency p-energy sums only strictly positive eigenvalues; real exponents p>0 and zero padding contribute zero. Pₙ is the literal n-vertex path, not a scalar sequence/model.

## Principal new results (all must be completed, not just one)
1. **Theorem 3.2, thm:positive-bipartite:** every connected bipartite n-vertex G, every real p≥2, E⁺ₚ(G)≥E⁺ₚ(Pₙ).
2. **Theorem 3.3, thm:positive-odd-integer:** every odd natural integer p≥3, every connected n-vertex G, same exact positive-energy bound. Natural odd p must be converted faithfully to the real exponent.
3. **Theorem 3.6, thm:positive-four-energy:** every connected n-vertex G, E⁺₄(G)≥E⁺₄(Pₙ). For n≥2 the actual path value is 3n−5; for n=1 it is zero. The proof gives strict inequality for non-trees; no weaker linear comparison is accepted.
4. **Theorem 3.7, thm:lap-signless-master:** every connected n-vertex G and every admissible third-order convex F:[0,∞)→ℝ, simultaneously ∑F(λᵢ(L(G)))≥∑F(λᵢ(L(Pₙ))) and ∑F(λᵢ(Q(G)))≥∑F(λᵢ(Q(Pₙ))). Literal admissibility: C² on the half-line, F″ absolutely continuous on each compact subinterval, F(0)=0, F′(0)≥0, F″(0)≥0, F‴≥0 almost everywhere on (0,∞). Do not replace AC or a.e. derivatives with stronger smoothness.
5. **Corollary 3.8, cor:lap-signless-powers:** same connected G, every real α≥1, both actual L/Q α-power sums ≥ corresponding path sums. Do not use the admissible class alone: powers for α∈[1,2) require the companion total-energy route.
6. **Corollary 3.10, cor:lap-signless-estrada:** every θ>0, both ∑exp(θλᵢ(L/Q(G))) ≥ path sums.
7. **Corollary 3.11, cor:lap-signless-resolvent:** RL(G)=∑1/(n+1−λᵢ(L(G))) and RQ(G)=∑1/(2n−1−λᵢ(Q(G))) ≥ path counterparts. Actual spectral denominator positivity must be proved, not assumed.
8. **Corollary 3.13, cor:thresholded-lap-signless:** every a≥0 and real p≥2, both ∑(λᵢ(L/Q(G))−a)₊ᵖ ≥ path sums; retain p=2 endpoint.
9. **Theorem 3.17, thm:edge-count-signless-stoploss:** every connected G with m≥1 actual edges, all t≥2, Ψₜ(G)=∑(λᵢ(Q(G))−t)₊²≥Ψₜ(Pₘ₊₁). Vertex count must not replace edge count.
10. **Theorem 3.18, thm:line-graph-positive-energy:** every connected G with m≥1 edges, all real p≥2, E⁺ₚ(actual line graph of G)≥E⁺ₚ(Pₘ). Path attainment supplies sharpness. Full shifted incidence spectral correspondence with multiplicity/zero padding is required.

Remark 3.9 tree-level L/Q second-order stop loss and Remark 3.19 line-graph positive square energy ≥m−1 are also retained as requested consequences. The paper does not claim the general positive-p conjecture or Radenković–Gutman Laplacian-energy conjecture. No unsupported equality iff is added to these new theorems.

## Necessary external source results, not permitted final hypotheses
Theorem 2.1 (companion Theorem1.3: total energy all p≥2 with p>2 equality iff path), Theorem2.3 (companion bipartite second-order squared singular-value stoploss), Corollary2.4 (admissible test comparison), Lemmas2.5–2.9 (rank-one trace formula, interval packing, path walk moments/envelopes, trigonometric pairs). Companion citation is arXiv:2605.22730v3. These are proof obligations unless a fully checked formal result can be reused; merely citing the paper or Sage certificate is not formal proof.

Also required: Cauchy/Loewner eigenvalue inequalities, unsigned incidence/subdivision/line-graph nonzero spectral multiset bridge; Clarkson–McCarthy Schatten inequality at 3 and positive-energy vertex gain real p≥3; real spectral shift calculus; convex majorization; actual path/cycle modes/trigonometric comparison; minimal deletion and graph structure; all AppendixA scalar and local-moment checks, infinite family moment stability; integrated stoploss→real p bridge.

## Initial library investigation
Actual mathlib incidence/LapMatrix/AdjMatrix and finite Hermitian Spectrum sources read, including real ordered eigenvalues and characteristic-polynomial roots with multiplicity. Their real formal proofs are viable reusable dependencies. TauCeti Schatten definition/triangle/ideal results were read but not imported: they do not directly provide the required Clarkson–McCarthy inequality or companion path theorem. Local filename/name search is not a community-wide nonexistence claim.

QuanyuTang/graph-p-energy-certificates @9ab79d5385f8c17579e4b6b51b31da92be4807da tree contains Sage scripts/logs, no Lean proof modules. The applications/verify_line_graph.sage file was read completely. It is reference/computation input only, never an axiom or proof dependency. No source author's review of this new Lean code is asserted; source-paper AI disclosure is not this formalization's model identification.
