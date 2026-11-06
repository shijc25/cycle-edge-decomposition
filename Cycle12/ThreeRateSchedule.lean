import Mathlib

namespace Cycle12
open Real
noncomputable section

theorem exists_geometric_stop_phase {X A theta : ℝ} (hA : 0<A) (hAX : A≤X)
    (htheta : 0<theta) (htheta1 : theta<1) :
    ∃ k : ℕ, A≤theta^k*X ∧ theta^k*X<A/theta := by
  have hX : 0<X := hA.trans_le hAX
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one (div_pos hA hX)
    ((div_le_one hX).mpr hAX) htheta htheta1
  refine ⟨k,(div_le_iff₀ hX).mp hhi,?_⟩
  apply (lt_div_iff₀ htheta).mpr
  have hh := (lt_div_iff₀ hX).mp hlo
  rw [pow_succ] at hh
  nlinarith only [hh]

/-- k+3 stages: theta2 is used through k+1, then theta1, then
theta0 controls the final remainder. -/
def threeRateLog (theta0 theta1 theta2 X : ℝ) (k i : ℕ) : ℝ :=
  if i≤k+1 then theta2^i*X
  else if i=k+2 then theta1*theta2^(k+1)*X
  else theta0*theta1*theta2^(k+1)*X

theorem three_rate_initial (theta0 theta1 theta2 X : ℝ) (k : ℕ) :
    threeRateLog theta0 theta1 theta2 X k 0=X := by
  simp [threeRateLog]

theorem three_rate_regular (theta0 theta1 theta2 X : ℝ) {k i : ℕ} (hi : i≤k+1) :
    threeRateLog theta0 theta1 theta2 X k i=theta2^i*X := by
  simp [threeRateLog,hi]

theorem three_rate_penultimate (theta0 theta1 theta2 X : ℝ) (k : ℕ) :
    threeRateLog theta0 theta1 theta2 X k (k+2)=theta1*theta2^(k+1)*X := by
  simp [threeRateLog]

theorem three_rate_final (theta0 theta1 theta2 X : ℝ) (k : ℕ) :
    threeRateLog theta0 theta1 theta2 X k (k+3)=theta0*theta1*theta2^(k+1)*X := by
  simp [threeRateLog]

theorem three_rate_steps (theta0 theta1 theta2 X : ℝ) (k : ℕ) :
    (∀ i≤k, threeRateLog theta0 theta1 theta2 X k (i+1)=
      theta2*threeRateLog theta0 theta1 theta2 X k i) ∧
    threeRateLog theta0 theta1 theta2 X k (k+2)=
      theta1*threeRateLog theta0 theta1 theta2 X k (k+1) ∧
    threeRateLog theta0 theta1 theta2 X k (k+3)=
      theta0*threeRateLog theta0 theta1 theta2 X k (k+2) := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [three_rate_regular _ _ _ _ (by omega),three_rate_regular _ _ _ _ (by omega),pow_succ]
    ring
  · rw [three_rate_penultimate,three_rate_regular _ _ _ _ le_rfl]
    ring
  · rw [three_rate_final,three_rate_penultimate]
    ring

theorem three_rate_active_lower {theta0 theta1 theta2 X A : ℝ} {k i : ℕ}
    (htheta : 0≤theta2) (htheta1 : theta2≤1) (hX : 0≤X)
    (hphase : A≤theta2^k*X) (hi : i≤k) :
    A≤threeRateLog theta0 theta1 theta2 X k i := by
  rw [three_rate_regular _ _ _ _ (by omega)]
  exact hphase.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one htheta htheta1 hi) hX)

theorem three_rate_boundary_lower {theta0 theta1 theta2 X A : ℝ} {k : ℕ}
    (htheta1 : 0≤theta1) (htheta2 : 0≤theta2) (hphase : A≤theta2^k*X) :
    theta2*A≤threeRateLog theta0 theta1 theta2 X k (k+1) ∧
    theta1*theta2*A≤threeRateLog theta0 theta1 theta2 X k (k+2) := by
  have h1 := mul_le_mul_of_nonneg_left hphase htheta2
  have h2 := mul_le_mul_of_nonneg_left h1 htheta1
  rw [three_rate_regular _ _ _ _ le_rfl,three_rate_penultimate,pow_succ]
  constructor <;> nlinarith only [h1,h2]

theorem three_rate_two_step {theta0 theta1 theta2 X : ℝ} {k i : ℕ}
    (htheta2 : 0≤theta2) (htheta : theta2≤theta1) (hX : 0≤X) (hi : i≤k) :
    theta2^2*threeRateLog theta0 theta1 theta2 X k i ≤
      threeRateLog theta0 theta1 theta2 X k (i+2) ∧
    threeRateLog theta0 theta1 theta2 X k (i+2) ≤
      theta1*theta2*threeRateLog theta0 theta1 theta2 X k i := by
  have hpow : 0≤theta2^i*X := mul_nonneg (pow_nonneg htheta2 _) hX
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htheta htheta2) hpow
  rw [three_rate_regular _ _ _ _ (by omega)]
  by_cases h : i<k
  · rw [three_rate_regular _ _ _ _ (by omega),pow_add]
    constructor <;> nlinarith only [hc]
  · have he : i=k := by omega
    subst i
    rw [three_rate_penultimate]
    simp only [pow_succ,pow_one,pow_zero]
    constructor <;> nlinarith only [hc]

end
end Cycle12
