module
public import Mathlib
/-! Exact scalar identities from the v1 Appendix and fifth-moment lower bound.
No scalar premise is asserted to have been derived from an actual graph spectrum. -/
@[expose] public section
namespace GraphPositiveEnergy

def Astar (t : ℝ) : ℝ := 2140 - 7*t^4
def Bstar (t : ℝ) : ℝ := 4414 - 4*t^4
def Kstar (t : ℝ) : ℝ := 5*(t^3 + 5*t^2 + 25*t + 125)
def qstar (x : ℝ) : ℝ := 64*x^5 + 240*x^4 + 472*x^3 + 603*x^2 + 512*x + 249

theorem shifted_qstar (t z : ℝ) :
    qstar (1-z)-t^4*(3+4*(1-z)) =
      Astar t - Bstar t*z + 4099*z^2 - 2072*z^3 + 560*z^4 - 64*z^5 := by
  unfold qstar Astar Bstar
  ring

theorem ratio_gap_identity (t : ℝ) :
    (1573/4090 : ℝ)*Bstar t - Astar t =
      (11169/2045 : ℝ)*(t-3)*(t+3)*(t^2+9) := by
  unfold Astar Bstar
  ring

theorem rational_margin :
    (4099 : ℝ)-2072*(1573/4090)-64*(1573/4090)^3-3000 =
      2552631003539/8552241125 := by norm_num

theorem Kstar_positive {t : ℝ} (ht : 3 ≤ t) : 0 < Kstar t := by
  unfold Kstar
  positivity

theorem fifth_order_factorization (y t : ℝ) :
    y^5-t^4*y = (y-t)*(y*(y+t)*(y^2+t^2)) := by ring

theorem fifth_order_scalar_lower {y t : ℝ} (hy : 0 ≤ y) (hy5 : y ≤ 5)
    (ht : 3 ≤ t) (_ht4 : t ≤ 4) :
    (y^5-t^4*y)/Kstar t ≤ max (y-t) 0 := by
  have hk := Kstar_positive ht
  apply (div_le_iff₀ hk).mpr
  rw [fifth_order_factorization]
  by_cases hyt : y ≤ t
  · rw [max_eq_right (sub_nonpos.mpr hyt), zero_mul]
    apply mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hyt)
    positivity
  · have hty : t < y := lt_of_not_ge hyt
    rw [max_eq_left (sub_nonneg.mpr hty.le)]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hty.le)
    calc y*(y+t)*(y^2+t^2) ≤ 5*(5+t)*(25+t^2) := by
           gcongr
           nlinarith only [hy,hy5]
         _ = Kstar t := by unfold Kstar; ring
end GraphPositiveEnergy
