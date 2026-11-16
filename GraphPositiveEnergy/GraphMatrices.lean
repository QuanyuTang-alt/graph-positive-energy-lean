module
public import Mathlib.Combinatorics.SimpleGraph.IncMatrix
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Star.Real

/-! Concrete finite graph matrices and their genuine multiplicity-counted spectra.
These are foundations, not proofs of path-minimality. -/
@[expose] public noncomputable section
namespace GraphPositiveEnergy
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Literal signless Laplacian D+A of a finite simple graph. -/
def signless (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  G.degMatrix ℝ + G.adjMatrix ℝ

/-- Unsigned incidence uses all unordered vertex pairs; nonedge columns are exactly zero.
This equality concerns the actual graph, not an assumed factorization. -/
theorem incidence_gram (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.incMatrix ℝ * (G.incMatrix ℝ)ᵀ = signless G := by
  rw [G.incMatrix_mul_transpose]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.of_apply, signless, Matrix.add_apply,
      SimpleGraph.degMatrix, diagonal_apply_eq, SimpleGraph.adjMatrix_apply,
      SimpleGraph.irrefl, ite_false, ite_true, add_zero]
  · simp only [Matrix.of_apply, ite_eq_right h, signless, Matrix.add_apply,
      SimpleGraph.degMatrix, diagonal_apply_ne _ h, SimpleGraph.adjMatrix_apply, zero_add]

/-- The actual signless Laplacian is positive semidefinite. -/
theorem signless_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj] :
    (signless G).PosSemidef := by
  rw [← incidence_gram]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (G.incMatrix ℝ)

/-- Real adjacency matrix powers have nonnegative entries: they count actual walks. -/
theorem adjacency_power_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ∀ i j, 0 ≤ ((G.adjMatrix ℝ)^k) i j := by
  intro i j
  rw [G.adjMatrix_pow_apply_eq_card_walk]
  exact Nat.cast_nonneg _

/-- Trace of a power of the actual adjacency matrix counts closed walks. -/
theorem adjacency_trace_power (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ((G.adjMatrix ℝ)^k).trace =
      ∑ v : V, (Fintype.card {p : G.Walk v v // p.length = k} : ℝ) := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro v _
  exact G.adjMatrix_pow_apply_eq_card_walk k v v

/-- Ordered actual adjacency eigenvalues with full multiplicity, via mathlib spectral theorem. -/
def adjacencyEigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (Fintype.card V) → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues₀

/-- Full source characterization: eigenvalues are the descending characteristic roots. -/
theorem adjacencyEigenvalues_characterization (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.adjMatrix ℝ).charpoly.roots).sort (· ≥ ·) = List.ofFn (adjacencyEigenvalues G) := by
  simpa only [adjacencyEigenvalues, RCLike.re_to_real, Multiset.map_id'] using
    (G.isHermitian_adjMatrix ℝ).sort_roots_charpoly_eq_eigenvalues₀

/-- The ordered spectrum really has all vertices, including zero modes. -/
theorem adjacencyEigenvalues_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    (List.ofFn (adjacencyEigenvalues G)).length = Fintype.card V := List.length_ofFn

/-- The spectral sequence is descending. -/
theorem adjacencyEigenvalues_antitone (G : SimpleGraph V) [DecidableRel G.Adj] :
    Antitone (adjacencyEigenvalues G) := (G.isHermitian_adjMatrix ℝ).eigenvalues₀_antitone

/-- Positive p-energy of the actual graph. The exponent is restricted to the paper's p>0 domain. -/
def positiveEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) (_hp : 0 < p) : ℝ :=
  ∑ i : Fin (Fintype.card V), (max (adjacencyEigenvalues G i) 0) ^ p

/-- Total p-energy of the actual graph on the paper's p>0 exponent domain. -/
def totalEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) (_hp : 0 < p) : ℝ :=
  ∑ i : Fin (Fintype.card V), |adjacencyEigenvalues G i| ^ p

/-- Trace of a genuine symmetric matrix power equals the sum of eigenvalue powers,
by unitary diagonalization. This supplies the actual operator bridge for closed-walk moments. -/
theorem trace_power_eq_eigenvalue_powers (M : Matrix V V ℝ) (hM : M.IsHermitian) (k : ℕ) :
    (M^k).trace = ∑ i : V, (hM.eigenvalues i)^k := by
  let D : Matrix V V ℝ := diagonal hM.eigenvalues
  let U := hM.eigenvectorUnitary
  have hm : M = Unitary.conjStarAlgAut ℝ _ U D := by
    simpa only [D, U, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hM.spectral_theorem
  conv_lhs => rw [hm, ← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  simp only [D, diagonal_pow, trace_diagonal, Pi.pow_apply]

/-- Nonnegative odd trace is a proved fact of the actual adjacency spectrum, not an assumption. -/
theorem adjacency_spectral_power_sum_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    0 ≤ ∑ i : V, ((G.isHermitian_adjMatrix ℝ).eigenvalues i)^k := by
  rw [← trace_power_eq_eigenvalue_powers]
  exact Finset.sum_nonneg (fun i _ => adjacency_power_nonneg G k i i)

end GraphPositiveEnergy
