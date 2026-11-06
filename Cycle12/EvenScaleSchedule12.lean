import Cycle12.EvenVariableLayers12
import Cycle12.GlobalBankPreparation12
import Cycle12.ScaleSchedule12
import Cycle12.ThreeRateSchedule
import Cycle12.ScaleHalflines12

namespace Cycle12.Even12
open Cycle12.Global12
open Real
noncomputable section

theorem entropy_schedule_step {X : ℝ} {k i : ℕ} (hX : 0≤X)
    (hphase : wA≤theta2^k*X) (hi : i<k+3) :
    (2:ℝ)^(s*logScale X k i)*((1001/1000:ℝ)+(rho-s)*logScale X k i) ≤
      (2:ℝ)^(logScale X k (i+1)) := by
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

def scaleData (X : ℝ) (k : ℕ) (hX : 0≤X) (hphase : wA≤theta2^k*X) : EvenEntropyScaleData where
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
    exact (bank_preparation_scale_bounds (logScale_minimum hX hphase hi)
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (rho*logScale X k i)) le_rfl).1
  expansion_square := by
    intro i hi
    exact (bank_preparation_scale_bounds (logScale_minimum hX hphase hi)
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (rho*logScale X k i)) le_rfl).2.1
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
end Cycle12.Even12
