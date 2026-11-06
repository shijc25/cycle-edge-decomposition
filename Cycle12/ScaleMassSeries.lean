import Cycle12.Foundations.ExponentialTails
import Cycle12.ThreeRateSchedule

namespace Cycle12
open Cycle13 Real Finset
noncomputable section

def scaleMassSeries (theta z : ℝ) : ℝ := ∑' j : ℕ, powerScaleTerm z theta j

theorem geometric_reverse_scale {theta X : ℝ} (htheta : 0<theta) {k i : ℕ} (hi : i≤k) :
    theta^i*X=(theta^k*X)*(theta⁻¹)^(k-i) := by
  have hp : theta^k=theta^i*theta^(k-i) := by
    rw [←pow_add,Nat.add_sub_of_le hi]
  rw [hp,inv_pow]
  have hn : theta^(k-i)≠0 := pow_ne_zero _ htheta.ne'
  field_simp

theorem geometric_scale_sum_bound {theta X A delta : ℝ}
    (htheta : 0<theta) (htheta1 : theta<1) (hA : 0<A) (hd : 0<delta)
    (k : ℕ) (hphase : A≤theta^k*X) :
    (∑ i∈Finset.range (k+1), (2:ℝ)^(-delta*(theta^i*X))) ≤
      scaleMassSeries theta (delta*A) := by
  have hpoint : ∀ i<k+1, (2:ℝ)^(-delta*(theta^i*X))≤
      powerScaleTerm (delta*A) theta (k-i) := by
    intro i hi
    rw [geometric_reverse_scale (k:=k) htheta (by omega)]
    unfold powerScaleTerm
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hphase (pow_nonneg (inv_nonneg.mpr htheta.le) (k-i))
    nlinarith only [mul_le_mul_of_nonneg_left hh hd.le]
  calc
    _ ≤ ∑ i∈Finset.range (k+1), powerScaleTerm (delta*A) theta (k-i) :=
      Finset.sum_le_sum (fun i hi => hpoint i (Finset.mem_range.mp hi))
    _ = ∑ i∈Finset.range (k+1), powerScaleTerm (delta*A) theta i := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (powerScaleTerm (delta*A) theta) (k+1)
    _ ≤ _ := (powerScaleSeries_summable (mul_pos hd hA) htheta htheta1).sum_le_tsum
      (Finset.range (k+1)) (fun i _ => Real.rpow_nonneg (by norm_num) _)

theorem three_rate_scale_sum_bound {theta0 theta1 theta2 X A delta : ℝ}
    (htheta1 : 0<theta1) (htheta2 : 0<theta2) (htheta21 : theta2<1)
    (hA : 0<A) (hd : 0<delta) (k : ℕ) (hphase : A≤theta2^k*X) :
    (∑ i∈Finset.range (k+3), (2:ℝ)^(-delta*threeRateLog theta0 theta1 theta2 X k i)) ≤
      (2:ℝ)^(-delta*(theta1*theta2*A))+scaleMassSeries theta2 (delta*(theta2*A)) := by
  have hnormal : theta2*A≤theta2^(k+1)*X := by
    have hh := mul_le_mul_of_nonneg_left hphase htheta2.le
    rw [pow_succ]
    nlinarith only [hh]
  have hsum := geometric_scale_sum_bound htheta2 htheta21 (mul_pos htheta2 hA) hd (k+1) hnormal
  have hlast := (three_rate_boundary_lower (theta0:=theta0) htheta1.le htheta2.le hphase).2
  have hlast' : (2:ℝ)^(-delta*threeRateLog theta0 theta1 theta2 X k (k+2)) ≤
      (2:ℝ)^(-delta*(theta1*theta2*A)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left hlast hd.le]
  have he : (∑ i∈Finset.range (k+2), (2:ℝ)^(-delta*threeRateLog theta0 theta1 theta2 X k i)) =
      ∑ i∈Finset.range (k+2), (2:ℝ)^(-delta*(theta2^i*X)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [three_rate_regular _ _ _ _ (by have := Finset.mem_range.mp hi; omega)]
  rw [show k+3=(k+2)+1 by omega,Finset.sum_range_succ,he]
  have hs' : (∑ i∈Finset.range (k+2), (2:ℝ)^(-delta*(theta2^i*X)))≤
      scaleMassSeries theta2 (delta*(theta2*A)) := by simpa only [Nat.add_assoc] using hsum
  linarith only [hs',hlast']

end
end Cycle12
