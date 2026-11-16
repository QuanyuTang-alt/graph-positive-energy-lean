module
public import Mathlib
public import GraphPositiveEnergy.GraphMatrices

/-! Exact finite local path-plus-leaf fifth moments.
All matrix equalities replay via kernel-checked ring normalization.
The infinite length stability and principal spectral comparison remain unproved. -/
@[expose] public section
namespace GraphPositiveEnergy
open Matrix

def localMatrix2 (x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![2 + 1*x, 1*x, 1, 1],
    ![1*x, 1 + 1*x, 1, 0],
    ![1, 1, 2, 0],
    ![1, 0, 0, 1]]
def localVector2 : Fin 4 → ℝ := ![1, 1, 0, 0]
def localIter2_1 (x : ℝ) : Fin 4 → ℝ := ![2 + 2*x, 1 + 2*x, 2, 1]
theorem local_step_2_1 (x : ℝ) : localMatrix2 x *ᵥ (localVector2) = localIter2_1 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix2, localVector2, localIter2_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter2_2 (x : ℝ) : Fin 4 → ℝ := ![7 + 7*x + 4*x^2, 3 + 5*x + 4*x^2, 7 + 4*x, 3 + 2*x]
theorem local_step_2_2 (x : ℝ) : localMatrix2 x *ᵥ (localIter2_1 x) = localIter2_2 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix2, localVector2, localIter2_1, localIter2_2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter2_3 (x : ℝ) : Fin 4 → ℝ := ![24 + 30*x + 20*x^2 + 8*x^3, 10 + 19*x + 16*x^2 + 8*x^3, 24 + 20*x + 8*x^2, 10 + 9*x + 4*x^2]
theorem local_step_2_3 (x : ℝ) : localMatrix2 x *ᵥ (localIter2_2 x) = localIter2_3 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix2, localVector2, localIter2_1, localIter2_2, localIter2_3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter2_4 (x : ℝ) : Fin 4 → ℝ := ![82 + 123*x + 101*x^2 + 52*x^3 + 16*x^4, 34 + 73*x + 73*x^2 + 44*x^3 + 16*x^4, 82 + 89*x + 52*x^2 + 16*x^3, 34 + 39*x + 24*x^2 + 8*x^3]
theorem local_step_2_4 (x : ℝ) : localMatrix2 x *ᵥ (localIter2_3 x) = localIter2_4 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix2, localVector2, localIter2_1, localIter2_2, localIter2_3, localIter2_4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter2_5 (x : ℝ) : Fin 4 → ℝ := ![280 + 490*x + 474*x^2 + 302*x^3 + 128*x^4 + 32*x^5, 116 + 278*x + 321*x^2 + 234*x^3 + 112*x^4 + 32*x^5, 280 + 374*x + 278*x^2 + 128*x^3 + 32*x^4, 116 + 162*x + 125*x^2 + 60*x^3 + 16*x^4]
theorem local_step_2_5 (x : ℝ) : localMatrix2 x *ᵥ (localIter2_4 x) = localIter2_5 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix2, localVector2, localIter2_1, localIter2_2, localIter2_3, localIter2_4, localIter2_5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem local_moment_2 (x : ℝ) :
    localVector2 ⬝ᵥ ((localMatrix2 x)^5 *ᵥ localVector2) = 396 + 768*x + 795*x^2 + 536*x^3 + 240*x^4 + 64*x^5 := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  rw [local_step_2_1, local_step_2_2, local_step_2_3, local_step_2_4, local_step_2_5]
  norm_num [localVector2, localIter2_5, dotProduct, Fin.sum_univ_succ]
  ring

def localGraph2 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun u v => (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 3))
instance : DecidableRel localGraph2.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (((u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 3)) ∨ ((v.val = 1 ∧ u.val = 2) ∨ (v.val = 2 ∧ u.val = 0) ∨ (v.val = 0 ∧ u.val = 3)))))
theorem local_degree_2 (i : Fin 4) : localGraph2.degree i = ![2, 1, 2, 1] i := by
  fin_cases i <;> decide
theorem localMatrix_graph_2 (x : ℝ) :
    localMatrix2 x = signless localGraph2 + x • vecMulVec localVector2 localVector2 := by
  ext i j
  simp only [signless, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply]
  simp_rw [local_degree_2]
  fin_cases i <;> fin_cases j
  all_goals norm_num [localMatrix2, localVector2, signless, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, localGraph2,
    SimpleGraph.fromRel_adj, Fin.sum_univ_succ, Matrix.vecMulVec]

def localMatrix3 (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![2 + 1*x, 1*x, 0, 1, 1],
    ![1*x, 1 + 1*x, 1, 0, 0],
    ![0, 1, 2, 1, 0],
    ![1, 0, 1, 2, 0],
    ![1, 0, 0, 0, 1]]
def localVector3 : Fin 5 → ℝ := ![1, 1, 0, 0, 0]
def localIter3_1 (x : ℝ) : Fin 5 → ℝ := ![2 + 2*x, 1 + 2*x, 1, 1, 1]
theorem local_step_3_1 (x : ℝ) : localMatrix3 x *ᵥ (localVector3) = localIter3_1 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix3, localVector3, localIter3_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter3_2 (x : ℝ) : Fin 5 → ℝ := ![6 + 7*x + 4*x^2, 2 + 5*x + 4*x^2, 4 + 2*x, 5 + 2*x, 3 + 2*x]
theorem local_step_3_2 (x : ℝ) : localMatrix3 x *ᵥ (localIter3_1 x) = localIter3_2 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix3, localVector3, localIter3_1, localIter3_2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter3_3 (x : ℝ) : Fin 5 → ℝ := ![20 + 26*x + 20*x^2 + 8*x^3, 6 + 15*x + 16*x^2 + 8*x^3, 15 + 11*x + 4*x^2, 20 + 13*x + 4*x^2, 9 + 9*x + 4*x^2]
theorem local_step_3_3 (x : ℝ) : localMatrix3 x *ᵥ (localIter3_2 x) = localIter3_3 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix3, localVector3, localIter3_1, localIter3_2, localIter3_3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter3_4 (x : ℝ) : Fin 5 → ℝ := ![69 + 100*x + 89*x^2 + 52*x^3 + 16*x^4, 21 + 52*x + 61*x^2 + 44*x^3 + 16*x^4, 56 + 50*x + 28*x^2 + 8*x^3, 75 + 63*x + 32*x^2 + 8*x^3, 29 + 35*x + 24*x^2 + 8*x^3]
theorem local_step_3_4 (x : ℝ) : localMatrix3 x *ᵥ (localIter3_3 x) = localIter3_4 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix3, localVector3, localIter3_1, localIter3_2, localIter3_3, localIter3_4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter3_5 (x : ℝ) : Fin 5 → ℝ := ![242 + 388*x + 386*x^2 + 270*x^3 + 128*x^4 + 32*x^5, 77 + 192*x + 241*x^2 + 202*x^3 + 112*x^4 + 32*x^5, 208 + 215*x + 149*x^2 + 68*x^3 + 16*x^4, 275 + 276*x + 181*x^2 + 76*x^3 + 16*x^4, 98 + 135*x + 113*x^2 + 60*x^3 + 16*x^4]
theorem local_step_3_5 (x : ℝ) : localMatrix3 x *ᵥ (localIter3_4 x) = localIter3_5 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix3, localVector3, localIter3_1, localIter3_2, localIter3_3, localIter3_4, localIter3_5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem local_moment_3 (x : ℝ) :
    localVector3 ⬝ᵥ ((localMatrix3 x)^5 *ᵥ localVector3) = 319 + 580*x + 627*x^2 + 472*x^3 + 240*x^4 + 64*x^5 := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  rw [local_step_3_1, local_step_3_2, local_step_3_3, local_step_3_4, local_step_3_5]
  norm_num [localVector3, localIter3_5, dotProduct, Fin.sum_univ_succ]
  ring

def localGraph3 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun u v => (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 4))
instance : DecidableRel localGraph3.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (((u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 4)) ∨ ((v.val = 1 ∧ u.val = 2) ∨ (v.val = 2 ∧ u.val = 3) ∨ (v.val = 3 ∧ u.val = 0) ∨ (v.val = 0 ∧ u.val = 4)))))
theorem local_degree_3 (i : Fin 5) : localGraph3.degree i = ![2, 1, 2, 2, 1] i := by
  fin_cases i <;> decide
theorem localMatrix_graph_3 (x : ℝ) :
    localMatrix3 x = signless localGraph3 + x • vecMulVec localVector3 localVector3 := by
  ext i j
  simp only [signless, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply]
  simp_rw [local_degree_3]
  fin_cases i <;> fin_cases j
  all_goals norm_num [localMatrix3, localVector3, signless, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, localGraph3,
    SimpleGraph.fromRel_adj, Fin.sum_univ_succ, Matrix.vecMulVec]

def localMatrix4 (x : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  ![![2 + 1*x, 1*x, 0, 0, 1, 1],
    ![1*x, 1 + 1*x, 1, 0, 0, 0],
    ![0, 1, 2, 1, 0, 0],
    ![0, 0, 1, 2, 1, 0],
    ![1, 0, 0, 1, 2, 0],
    ![1, 0, 0, 0, 0, 1]]
def localVector4 : Fin 6 → ℝ := ![1, 1, 0, 0, 0, 0]
def localIter4_1 (x : ℝ) : Fin 6 → ℝ := ![2 + 2*x, 1 + 2*x, 1, 0, 1, 1]
theorem local_step_4_1 (x : ℝ) : localMatrix4 x *ᵥ (localVector4) = localIter4_1 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix4, localVector4, localIter4_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter4_2 (x : ℝ) : Fin 6 → ℝ := ![6 + 7*x + 4*x^2, 2 + 5*x + 4*x^2, 3 + 2*x, 2, 4 + 2*x, 3 + 2*x]
theorem local_step_4_2 (x : ℝ) : localMatrix4 x *ᵥ (localIter4_1 x) = localIter4_2 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix4, localVector4, localIter4_1, localIter4_2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter4_3 (x : ℝ) : Fin 6 → ℝ := ![19 + 26*x + 20*x^2 + 8*x^3, 5 + 15*x + 16*x^2 + 8*x^3, 10 + 9*x + 4*x^2, 11 + 4*x, 16 + 11*x + 4*x^2, 9 + 9*x + 4*x^2]
theorem local_step_4_3 (x : ℝ) : localMatrix4 x *ᵥ (localIter4_2 x) = localIter4_3 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix4, localVector4, localIter4_1, localIter4_2, localIter4_3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter4_4 (x : ℝ) : Fin 6 → ℝ := ![63 + 96*x + 89*x^2 + 52*x^3 + 16*x^4, 15 + 48*x + 61*x^2 + 44*x^3 + 16*x^4, 36 + 37*x + 24*x^2 + 8*x^3, 48 + 28*x + 8*x^2, 62 + 52*x + 28*x^2 + 8*x^3, 28 + 35*x + 24*x^2 + 8*x^3]
theorem local_step_4_4 (x : ℝ) : localMatrix4 x *ᵥ (localIter4_3 x) = localIter4_4 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix4, localVector4, localIter4_1, localIter4_2, localIter4_3, localIter4_4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter4_5 (x : ℝ) : Fin 6 → ℝ := ![216 + 357*x + 374*x^2 + 270*x^3 + 128*x^4 + 32*x^5, 51 + 163*x + 229*x^2 + 202*x^3 + 112*x^4 + 32*x^5, 135 + 150*x + 117*x^2 + 60*x^3 + 16*x^4, 194 + 145*x + 68*x^2 + 16*x^3, 235 + 228*x + 153*x^2 + 68*x^3 + 16*x^4, 91 + 131*x + 113*x^2 + 60*x^3 + 16*x^4]
theorem local_step_4_5 (x : ℝ) : localMatrix4 x *ᵥ (localIter4_4 x) = localIter4_5 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix4, localVector4, localIter4_1, localIter4_2, localIter4_3, localIter4_4, localIter4_5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem local_moment_4 (x : ℝ) :
    localVector4 ⬝ᵥ ((localMatrix4 x)^5 *ᵥ localVector4) = 267 + 520*x + 603*x^2 + 472*x^3 + 240*x^4 + 64*x^5 := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  rw [local_step_4_1, local_step_4_2, local_step_4_3, local_step_4_4, local_step_4_5]
  norm_num [localVector4, localIter4_5, dotProduct, Fin.sum_univ_succ]
  ring

def localGraph4 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun u v => (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 5))
instance : DecidableRel localGraph4.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (((u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 5)) ∨ ((v.val = 1 ∧ u.val = 2) ∨ (v.val = 2 ∧ u.val = 3) ∨ (v.val = 3 ∧ u.val = 4) ∨ (v.val = 4 ∧ u.val = 0) ∨ (v.val = 0 ∧ u.val = 5)))))
theorem local_degree_4 (i : Fin 6) : localGraph4.degree i = ![2, 1, 2, 2, 2, 1] i := by
  fin_cases i <;> decide
theorem localMatrix_graph_4 (x : ℝ) :
    localMatrix4 x = signless localGraph4 + x • vecMulVec localVector4 localVector4 := by
  ext i j
  simp only [signless, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply]
  simp_rw [local_degree_4]
  fin_cases i <;> fin_cases j
  all_goals norm_num [localMatrix4, localVector4, signless, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, localGraph4,
    SimpleGraph.fromRel_adj, Fin.sum_univ_succ, Matrix.vecMulVec]

def localMatrix5 (x : ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  ![![2 + 1*x, 1*x, 0, 0, 0, 1, 1],
    ![1*x, 1 + 1*x, 1, 0, 0, 0, 0],
    ![0, 1, 2, 1, 0, 0, 0],
    ![0, 0, 1, 2, 1, 0, 0],
    ![0, 0, 0, 1, 2, 1, 0],
    ![1, 0, 0, 0, 1, 2, 0],
    ![1, 0, 0, 0, 0, 0, 1]]
def localVector5 : Fin 7 → ℝ := ![1, 1, 0, 0, 0, 0, 0]
def localIter5_1 (x : ℝ) : Fin 7 → ℝ := ![2 + 2*x, 1 + 2*x, 1, 0, 0, 1, 1]
theorem local_step_5_1 (x : ℝ) : localMatrix5 x *ᵥ (localVector5) = localIter5_1 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix5, localVector5, localIter5_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter5_2 (x : ℝ) : Fin 7 → ℝ := ![6 + 7*x + 4*x^2, 2 + 5*x + 4*x^2, 3 + 2*x, 1, 1, 4 + 2*x, 3 + 2*x]
theorem local_step_5_2 (x : ℝ) : localMatrix5 x *ᵥ (localIter5_1 x) = localIter5_2 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix5, localVector5, localIter5_1, localIter5_2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter5_3 (x : ℝ) : Fin 7 → ℝ := ![19 + 26*x + 20*x^2 + 8*x^3, 5 + 15*x + 16*x^2 + 8*x^3, 9 + 9*x + 4*x^2, 6 + 2*x, 7 + 2*x, 15 + 11*x + 4*x^2, 9 + 9*x + 4*x^2]
theorem local_step_5_3 (x : ℝ) : localMatrix5 x *ᵥ (localIter5_2 x) = localIter5_3 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix5, localVector5, localIter5_1, localIter5_2, localIter5_3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter5_4 (x : ℝ) : Fin 7 → ℝ := ![62 + 96*x + 89*x^2 + 52*x^3 + 16*x^4, 14 + 48*x + 61*x^2 + 44*x^3 + 16*x^4, 29 + 35*x + 24*x^2 + 8*x^3, 28 + 15*x + 4*x^2, 35 + 17*x + 4*x^2, 56 + 50*x + 28*x^2 + 8*x^3, 28 + 35*x + 24*x^2 + 8*x^3]
theorem local_step_5_4 (x : ℝ) : localMatrix5 x *ᵥ (localIter5_3 x) = localIter5_4 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix5, localVector5, localIter5_1, localIter5_2, localIter5_3, localIter5_4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter5_5 (x : ℝ) : Fin 7 → ℝ := ![208 + 353*x + 374*x^2 + 270*x^3 + 128*x^4 + 32*x^5, 43 + 159*x + 229*x^2 + 202*x^3 + 112*x^4 + 32*x^5, 100 + 133*x + 113*x^2 + 60*x^3 + 16*x^4, 120 + 82*x + 36*x^2 + 8*x^3, 154 + 99*x + 40*x^2 + 8*x^3, 209 + 213*x + 149*x^2 + 68*x^3 + 16*x^4, 90 + 131*x + 113*x^2 + 60*x^3 + 16*x^4]
theorem local_step_5_5 (x : ℝ) : localMatrix5 x *ᵥ (localIter5_4 x) = localIter5_5 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix5, localVector5, localIter5_1, localIter5_2, localIter5_3, localIter5_4, localIter5_5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem local_moment_5 (x : ℝ) :
    localVector5 ⬝ᵥ ((localMatrix5 x)^5 *ᵥ localVector5) = 251 + 512*x + 603*x^2 + 472*x^3 + 240*x^4 + 64*x^5 := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  rw [local_step_5_1, local_step_5_2, local_step_5_3, local_step_5_4, local_step_5_5]
  norm_num [localVector5, localIter5_5, dotProduct, Fin.sum_univ_succ]
  ring

def localGraph5 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun u v => (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 5) ∨ (u.val = 5 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 6))
instance : DecidableRel localGraph5.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (((u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 5) ∨ (u.val = 5 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 6)) ∨ ((v.val = 1 ∧ u.val = 2) ∨ (v.val = 2 ∧ u.val = 3) ∨ (v.val = 3 ∧ u.val = 4) ∨ (v.val = 4 ∧ u.val = 5) ∨ (v.val = 5 ∧ u.val = 0) ∨ (v.val = 0 ∧ u.val = 6)))))
theorem local_degree_5 (i : Fin 7) : localGraph5.degree i = ![2, 1, 2, 2, 2, 2, 1] i := by
  fin_cases i <;> decide
theorem localMatrix_graph_5 (x : ℝ) :
    localMatrix5 x = signless localGraph5 + x • vecMulVec localVector5 localVector5 := by
  ext i j
  simp only [signless, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply]
  simp_rw [local_degree_5]
  fin_cases i <;> fin_cases j
  all_goals norm_num [localMatrix5, localVector5, signless, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, localGraph5,
    SimpleGraph.fromRel_adj, Fin.sum_univ_succ, Matrix.vecMulVec]

def localMatrix6 (x : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![2 + 1*x, 1*x, 0, 0, 0, 0, 1, 1],
    ![1*x, 1 + 1*x, 1, 0, 0, 0, 0, 0],
    ![0, 1, 2, 1, 0, 0, 0, 0],
    ![0, 0, 1, 2, 1, 0, 0, 0],
    ![0, 0, 0, 1, 2, 1, 0, 0],
    ![0, 0, 0, 0, 1, 2, 1, 0],
    ![1, 0, 0, 0, 0, 1, 2, 0],
    ![1, 0, 0, 0, 0, 0, 0, 1]]
def localVector6 : Fin 8 → ℝ := ![1, 1, 0, 0, 0, 0, 0, 0]
def localIter6_1 (x : ℝ) : Fin 8 → ℝ := ![2 + 2*x, 1 + 2*x, 1, 0, 0, 0, 1, 1]
theorem local_step_6_1 (x : ℝ) : localMatrix6 x *ᵥ (localVector6) = localIter6_1 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix6, localVector6, localIter6_1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter6_2 (x : ℝ) : Fin 8 → ℝ := ![6 + 7*x + 4*x^2, 2 + 5*x + 4*x^2, 3 + 2*x, 1, 0, 1, 4 + 2*x, 3 + 2*x]
theorem local_step_6_2 (x : ℝ) : localMatrix6 x *ᵥ (localIter6_1 x) = localIter6_2 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix6, localVector6, localIter6_1, localIter6_2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter6_3 (x : ℝ) : Fin 8 → ℝ := ![19 + 26*x + 20*x^2 + 8*x^3, 5 + 15*x + 16*x^2 + 8*x^3, 9 + 9*x + 4*x^2, 5 + 2*x, 2, 6 + 2*x, 15 + 11*x + 4*x^2, 9 + 9*x + 4*x^2]
theorem local_step_6_3 (x : ℝ) : localMatrix6 x *ᵥ (localIter6_2 x) = localIter6_3 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix6, localVector6, localIter6_1, localIter6_2, localIter6_3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter6_4 (x : ℝ) : Fin 8 → ℝ := ![62 + 96*x + 89*x^2 + 52*x^3 + 16*x^4, 14 + 48*x + 61*x^2 + 44*x^3 + 16*x^4, 28 + 35*x + 24*x^2 + 8*x^3, 21 + 13*x + 4*x^2, 15 + 4*x, 29 + 15*x + 4*x^2, 55 + 50*x + 28*x^2 + 8*x^3, 28 + 35*x + 24*x^2 + 8*x^3]
theorem local_step_6_4 (x : ℝ) : localMatrix6 x *ᵥ (localIter6_3 x) = localIter6_4 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix6, localVector6, localIter6_1, localIter6_2, localIter6_3, localIter6_4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

def localIter6_5 (x : ℝ) : Fin 8 → ℝ := ![207 + 353*x + 374*x^2 + 270*x^3 + 128*x^4 + 32*x^5, 42 + 159*x + 229*x^2 + 202*x^3 + 112*x^4 + 32*x^5, 91 + 131*x + 113*x^2 + 60*x^3 + 16*x^4, 85 + 65*x + 32*x^2 + 8*x^3, 80 + 36*x + 8*x^2, 128 + 84*x + 36*x^2 + 8*x^3, 201 + 211*x + 149*x^2 + 68*x^3 + 16*x^4, 90 + 131*x + 113*x^2 + 60*x^3 + 16*x^4]
theorem local_step_6_5 (x : ℝ) : localMatrix6 x *ᵥ (localIter6_4 x) = localIter6_5 x := by
  ext i
  fin_cases i
  all_goals norm_num [localMatrix6, localVector6, localIter6_1, localIter6_2, localIter6_3, localIter6_4, localIter6_5, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem local_moment_6 (x : ℝ) :
    localVector6 ⬝ᵥ ((localMatrix6 x)^5 *ᵥ localVector6) = 249 + 512*x + 603*x^2 + 472*x^3 + 240*x^4 + 64*x^5 := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  rw [local_step_6_1, local_step_6_2, local_step_6_3, local_step_6_4, local_step_6_5]
  norm_num [localVector6, localIter6_5, dotProduct, Fin.sum_univ_succ]
  ring

def localGraph6 : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (fun u v => (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 5) ∨ (u.val = 5 ∧ v.val = 6) ∨ (u.val = 6 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 7))
instance : DecidableRel localGraph6.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (((u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 5) ∨ (u.val = 5 ∧ v.val = 6) ∨ (u.val = 6 ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val = 7)) ∨ ((v.val = 1 ∧ u.val = 2) ∨ (v.val = 2 ∧ u.val = 3) ∨ (v.val = 3 ∧ u.val = 4) ∨ (v.val = 4 ∧ u.val = 5) ∨ (v.val = 5 ∧ u.val = 6) ∨ (v.val = 6 ∧ u.val = 0) ∨ (v.val = 0 ∧ u.val = 7)))))
theorem local_degree_6 (i : Fin 8) : localGraph6.degree i = ![2, 1, 2, 2, 2, 2, 2, 1] i := by
  fin_cases i <;> decide
theorem localMatrix_graph_6 (x : ℝ) :
    localMatrix6 x = signless localGraph6 + x • vecMulVec localVector6 localVector6 := by
  ext i j
  simp only [signless, Matrix.add_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply]
  simp_rw [local_degree_6]
  fin_cases i <;> fin_cases j
  all_goals norm_num [localMatrix6, localVector6, signless, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, localGraph6,
    SimpleGraph.fromRel_adj, Fin.sum_univ_succ, Matrix.vecMulVec]

end GraphPositiveEnergy
