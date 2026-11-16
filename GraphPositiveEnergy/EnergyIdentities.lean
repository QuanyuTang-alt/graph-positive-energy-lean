module
public import GraphPositiveEnergy.GraphMatrices
import Mathlib

/-! Actual multiplicity-counted graph energy identities. No path comparison is assumed. -/
@[expose] public noncomputable section
namespace GraphPositiveEnergy
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Positive energy equals the literal strictly-positive-eigenvalue filtered sum. -/
theorem positiveEnergy_eq_filtered (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℝ) (hp : 0 < p) :
    positiveEnergy G p hp =
      ∑ i ∈ Finset.univ.filter (fun i => 0 < adjacencyEigenvalues G i),
        (adjacencyEigenvalues G i)^p := by
  unfold positiveEnergy
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < adjacencyEigenvalues G i
  · rw [ite_eq_left h, max_eq_left h.le]
  · rw [ite_eq_right h, max_eq_right (le_of_not_gt h), Real.zero_rpow hp.ne']

/-- Reindex the complete actual spectrum from vertices to its ordered Fin index. -/
theorem spectral_sum_reindex (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℝ → ℝ) :
    (∑ i : V, f ((G.isHermitian_adjMatrix ℝ).eigenvalues i)) =
      ∑ i : Fin (Fintype.card V), f (adjacencyEigenvalues G i) := by
  let e : V ≃ Fin (Fintype.card V) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  exact Fintype.sum_equiv e _ _ (fun i => rfl)

/-- For odd integer exponents, actual positive energy controls half actual total energy.
The closed-walk nonnegative trace is proved from the actual graph, not an extra premise. -/
theorem odd_positive_energy_half_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : Odd k) (hkpos : 0 < k) :
    totalEnergy G (k : ℝ) (by exact_mod_cast hkpos) ≤
      2*positiveEnergy G (k : ℝ) (by exact_mod_cast hkpos) := by
  have hscalar (x : ℝ) : |x|^k+x^k = 2*(max x 0)^k := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx]
      ring
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [abs_of_nonpos hx', hk.neg_pow, max_eq_right hx', zero_pow (Nat.ne_of_gt hkpos)]
      ring
  have hs : (∑ i : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|^k)+
      (∑ i : V, ((G.isHermitian_adjMatrix ℝ).eigenvalues i)^k) =
      2*(∑ i : V, (max ((G.isHermitian_adjMatrix ℝ).eigenvalues i) 0)^k) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hscalar _)
  have hnon := adjacency_spectral_power_sum_nonneg G k
  have hle : (∑ i : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|^k) ≤
      2*(∑ i : V, (max ((G.isHermitian_adjMatrix ℝ).eigenvalues i) 0)^k) := by
    linarith only [hs,hnon]
  rw [spectral_sum_reindex G (fun x => |x|^k),
    spectral_sum_reindex G (fun x => (max x 0)^k)] at hle
  simpa only [totalEnergy,positiveEnergy,Real.rpow_natCast] using hle
end GraphPositiveEnergy
