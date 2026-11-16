# P29 graph positive energy — checked partial foundations

Original paper authors (source order): **Yinchen Liu, Quanyu Tang**.
**形式化进行中，尚未完成，未达到 Palomar 提交标准。**
Project contributor and responsible maintainer: **Quanyu Tang**; Lean implementation assisted by **Doubao Work**. No independent human reviewer or source-author code endorsement is claimed.

Source: *Path-Minimality for Positive p-Energies, Laplacian-Type Spectra, and Line Graphs*, latest checked **arXiv:2606.30996v1**. Live submission history and unversioned PDF agree; v1 is the current release, not an automatic choice of the oldest version. Full 24-page paper / 2367-line TeX, appendix and bibliography were read. Original manuscript files are not distributed.

## Status B — no principal path-minimality theorem is complete
None of Theorems **3.2, 3.3, 3.6, 3.7, 3.17, 3.18** or application Corollaries **3.8, 3.10, 3.11, 3.13** has been unconditionally formalized. The companion-paper path-minimality and stop-loss inputs are not assumed or fabricated. The actual adjacency/Laplacian/signless/line-graph spectral comparisons and sharp path attainment remain open.

## What is genuinely proved
The current support tree has **76 complete theorems and 60 definitions**, including intermediate finite certificate steps. This count is not a count of principal results. All 136 declarations have dedicated axiom audit output; only `propext`, `Classical.choice`, `Quot.sound` occur.

- **GraphMatrices (9 theorems, 4 definitions):** actual signless Laplacian D+A, genuine incidence Gram identity and PSD; adjacency matrix powers/trace count walks; actual ordered adjacency eigenvalues characterized by full characteristic-polynomial roots (with multiplicity and zero modes); symmetric matrix trace powers equal sums of actual eigenvalue powers; adjacency spectral power sums are nonnegative. This is an actual finite operator bridge, not an arbitrary numerical spectrum.
- **EnergyIdentities (3 theorems):** actual positive energy equals the strictly-positive filtered sum for every p>0; complete spectrum reindexing; actual odd-integer positive energy ≥half actual total energy, derived using the proved closed-walk trace. It is not the missing path-minimality comparison.
- **ScalarChecks (6 theorems, 4 definitions):** exact q-shift/ratio/margin polynomial identities and fifth-order scalar lower bound on the specified window, with no graph moment assumed to have been established.
- **LocalMoments (40 theorems, 40 definitions):** five real finite matrices for the Appendix models L=2,…,6; 25 verified matvec steps, five exact fifth moments, five actual finite simple graph degree formulas and five matrix=actual signless graph+rank-one update identities. Kernel `decide` checks small finite graph degree facts. These are not the arbitrary-L stability theorem or the deletion-minimal comparison.
- **EnvelopeCertificates (18 theorems, 12 definitions):** six exact rational Bernstein decompositions, six interval nonnegativity results and six identities matching the original scalar envelope formulas. Coefficients are generated in Python but every identity and positivity is checked by Lean. This does not prove spectral envelope inputs or feed them into a principal theorem.

No production proof uses unfinished holes, new axioms, native_decide or native evaluation certificates. No draft principal theorem is imported. The proof files are Lean modules with exposed literal meaning-carrying definitions and `autoImplicit=false`.

## Reproduce supporting validation
Lean `leanprover/lean4:v4.36.0-rc2`; mathlib `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`, with all public transitive Git revisions fixed in lake-manifest.json. TauCeti is **not** a P29 dependency; its Schatten file was inspected only.

```sh
lake exe cache get
lake build
lake env lean verification/Audit.lean
python3 scripts/check_progress.py
```

Optional deterministic regeneration of finite certificates (standard Python library only) followed by Lean validation:

```sh
python3 scripts/generate_local_moments.py
python3 scripts/generate_envelopes.py
lake build
lake env lean verification/Audit.lean
```

Committed logs are development-checkout support validation using the pinned mathlib cache. They do not certify an isolated clean-checkout principal acceptance. No principal Challenge/Solution/Comparator is fabricated; Comparator **not run**. No Actions workflow ships; repository Actions **disabled**, no CI run intended. This is not Palomar-ready and has not been submitted or registered.

## Gaps and scope
See [complete source inventory](docs/SOURCE-AND-SEMANTICS.md), [next steps and actual attempts](docs/NEXT-STEPS.md), and [support semantics](docs/SUPPORT-SEMANTICS.md). Remaining work includes companion total-energy/bipartite stop-loss theorem, actual path/cycle spectra, bipartite and incidence/subdivision/line-graph multiset bridges, Schatten Clarkson–McCarthy vertex gain, a.e./AC admissible-function semantics, spectral shift differentiation and packing, arbitrary local moment stability, structural deletion and real-p integrated comparisons.

[Errata and deviations](docs/ERRATA-AND-DEVIATIONS.md): 0 asserted source errata, 3 scope/representation/certificate-route deviations. Missing formal infrastructure is not a claim that the paper is incorrect. No independent reviewer was used.

## AI, provenance and license
Doubao Work assisted reading the original informal proof, library search, proof writing/repair and same-assistant semantic review; Lean/Lake perform kernel checking; Python emits exact finite certificate statements; GitHub CLI publishes the progress. No verifiable model identifier is available, so metadata records `models: []`; none is guessed. Original paper and external repositories' AI disclosures are not tools executed in this project. No actual human/source-author code review is claimed. Code Apache-2.0; see LICENSE and NOTICE. No original TeX/PDF/CV, credentials, caches or private work records are distributed.
