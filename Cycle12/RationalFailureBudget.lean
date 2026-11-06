import Cycle12.RationalDecay

namespace Cycle12
open Real

structure RatFailureBudget where
  scaleLower : ℚ
  omega : ℚ
  bound : ℚ
  terms : List (ℚ × RatDecayCertificate)

def RatFailureBudget.NumericValid (c : RatFailureBudget) : Prop :=
  0 < c.omega ∧ (∀ t∈c.terms, 0 ≤ t.1 ∧ t.2.scaleLower ≤ c.scaleLower) ∧
    (c.terms.map (fun t => t.1*t.2.bound)).sum ≤ c.omega*c.bound

instance instDecidableRatFailureBudgetNumeric (c : RatFailureBudget) : Decidable c.NumericValid := by
  unfold RatFailureBudget.NumericValid
  infer_instance

noncomputable section

def RatFailureBudget.Sound (c : RatFailureBudget) : Prop :=
  ∀ R : ℝ, (c.scaleLower:ℝ) ≤ R →
    ((c.terms.map (fun t => (t.1:ℝ)*exp (-(t.2.exponent:ℝ)*R))).sum)/(c.omega:ℝ) ≤ (c.bound:ℝ)

theorem rat_failure_budget_sound (c : RatFailureBudget)
    (ha : ∀ t∈c.terms, t.2.Sound) (hc : c.NumericValid) : c.Sound := by
  intro R hR
  have hsum : (c.terms.map (fun t => (t.1:ℝ)*exp (-(t.2.exponent:ℝ)*R))).sum ≤
      (c.terms.map (fun t => (t.1:ℝ)*(t.2.bound:ℝ))).sum := by
    apply List.sum_le_sum
    intro a haMem
    exact mul_le_mul_of_nonneg_left (ha a haMem R
      (((Rat.cast_le (K:=ℝ)).mpr (hc.2.1 a haMem).2).trans hR))
      ((Rat.cast_nonneg (K:=ℝ)).mpr (hc.2.1 a haMem).1)
  have hb := (Rat.cast_le (K:=ℝ)).mpr hc.2.2
  simp only [Rat.cast_mul] at hb
  have hcast : (((c.terms.map (fun t => t.1*t.2.bound)).sum:ℚ):ℝ)=
      (c.terms.map (fun t => (t.1:ℝ)*(t.2.bound:ℝ))).sum := by
    simp only [Rat.cast_list_sum,List.map_map,Function.comp_def,Rat.cast_mul]
  rw [hcast] at hb
  exact (div_le_iff₀ (show (0:ℝ) < (c.omega:ℝ) by exact_mod_cast hc.1)).mpr (by
    simpa only [mul_comm] using hsum.trans hb)

end
end Cycle12
