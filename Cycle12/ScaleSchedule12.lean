import Cycle12.VariableScaleLayers
import Cycle12.ThreeRateSchedule
import Cycle12.ScaleHalflines12

namespace Cycle12.Global12
open Real
noncomputable section

def logScale (X : ℝ) (k i : ℕ) : ℝ := threeRateLog theta0 theta1 theta2 X k i

theorem logScale_active {X : ℝ} {k i : ℕ} (hX : 0≤X)
    (hphase : wA≤theta2^k*X) (hi : i≤k) : wA≤logScale X k i :=
  three_rate_active_lower (by norm_num [theta2]) (by norm_num [theta2]) hX hphase hi

theorem logScale_boundary {X : ℝ} {k : ℕ} (hphase : wA≤theta2^k*X) :
    w0/theta1≤logScale X k (k+1) ∧ w0≤logScale X k (k+2) := by
  have hh := three_rate_boundary_lower (theta0:=theta0) (theta1:=theta1) (theta2:=theta2)
    (by norm_num [theta1])
    (by norm_num [theta2]) hphase
  have he1 : theta2*wA=w0/theta1 := by norm_num [theta2,wA,w0,theta1]
  have he2 : theta1*theta2*wA=w0 := by norm_num [theta1,theta2,wA,w0]
  simpa only [he1,he2,logScale] using hh

theorem logScale_minimum {X : ℝ} {k i : ℕ} (hX : 0≤X)
    (hphase : wA≤theta2^k*X) (hi : i<k+3) : w0≤logScale X k i := by
  by_cases h : i≤k
  · exact (show w0≤wA by norm_num [w0,wA]).trans (logScale_active hX hphase h)
  · have hb := logScale_boundary hphase
    rcases (by omega : i=k+1 ∨ i=k+2) with rfl | rfl
    · exact (show w0≤w0/theta1 by norm_num [w0,theta1]).trans hb.1
    · exact hb.2

theorem logScale_positive {X : ℝ} {k i : ℕ} (hX : 0≤X)
    (hphase : wA≤theta2^k*X) (hi : i<k+3) : 0<logScale X k i :=
  (show 0<w0 by norm_num [w0]).trans_le (logScale_minimum hX hphase hi)

theorem entropy_schedule_step {X : ℝ} {k i : ℕ} (hX : 0≤X)
    (hphase : wA≤theta2^k*X) (hi : i<k+3) :
    (2:ℝ)^(s*logScale X k i)*(1+(rho-s)*logScale X k i) ≤
      (2:ℝ)^(logScale X k (i+1)) := by
  have hpad : (2:ℝ)^(s*logScale X k i)*(1+(rho-s)*logScale X k i) ≤
      (2:ℝ)^(s*logScale X k i)*((1001/1000:ℝ)+(rho-s)*logScale X k i) := by
    apply mul_le_mul_of_nonneg_left (by linarith)
      (Real.rpow_nonneg (by norm_num) _)
  apply hpad.trans
  have hsteps := three_rate_steps theta0 theta1 theta2 X k
  by_cases h : i≤k
  · change _≤(2:ℝ)^(threeRateLog theta0 theta1 theta2 X k (i+1))
    rw [hsteps.1 i h]
    exact entropy_halfline2 (logScale_active hX hphase h)
  · have hb := logScale_boundary hphase
    rcases (by omega : i=k+1 ∨ i=k+2) with rfl | rfl
    · change _≤(2:ℝ)^(threeRateLog theta0 theta1 theta2 X k (k+2))
      rw [hsteps.2.1]
      exact entropy_halfline1 hb.1
    · change _≤(2:ℝ)^(threeRateLog theta0 theta1 theta2 X k (k+3))
      rw [hsteps.2.2]
      exact entropy_halfline0 hb.2

def scaleData (X : ℝ) (k : ℕ) (hX : 0≤X) (hphase : wA≤theta2^k*X) : EntropyScaleData where
  degree := fun i => (2:ℝ)^(logScale X k i)
  cycleLength := fun i => (2:ℝ)^((1+eps)*logScale X k i)
  boxOrder := fun i => (2:ℝ)^(rho*logScale X k i)
  expansion := fun i => (2:ℝ)^(s*logScale X k i)
  valid := fun i => i<k+3
  cycle_pos := by
    intro i hi
    exact Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num [eps])
      (logScale_positive hX hphase hi).le)
  room := fun i hi => (overlap_halfline (logScale_minimum hX hphase hi)).1
  expansion_pos := by
    intro i hi
    exact Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num [s])
      (logScale_positive hX hphase hi).le)
  expansion_le := by
    intro i hi
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by norm_num [s,rho]) (logScale_positive hX hphase hi).le)
  next_degree := by
    intro i hi
    rw [entropy_power_rate]
    exact entropy_schedule_step hX hphase hi

theorem scaleData_overlap {X : ℝ} {k i : ℕ} (hX : 0≤X)
    (hphase : wA≤theta2^k*X) (hi : i<k+3) :
    (scaleData X k hX hphase).overlap i≤overlap*(2:ℝ)^(-delta*logScale X k i) :=
  (overlap_halfline (logScale_minimum hX hphase hi)).2

end
end Cycle12.Global12
