import Mathlib

/-! Integrating a cumulative exponential counting bound gives the sharp
finite union budget, without rounding the size parameter to bins. -/
namespace Cycle13
open Finset Real MeasureTheory Set
noncomputable section
attribute [local instance] Classical.propDecidable

theorem finite_exponential_counting_tail {I : Type} (C : Finset I) (x : I→ℝ)
    {lam a b : ℝ} (hb : 0 < b) (hba : a < b)
    (hmin : ∀ i∈C, lam ≤ x i)
    (hcount : ∀ t, lam ≤ t → ((C.filter (fun i => x i ≤ t)).card:ℝ) ≤ exp (a*t)) :
    (∑ i∈C, exp (-b*x i)) ≤ b/(b-a)*exp (-(b-a)*lam) := by
  let term : I→ℝ→ℝ := fun i => (Ioi (x i)).indicator (fun t => b*exp (-b*t))
  have hi : ∀ i, IntegrableOn (term i) (Ioi lam) := by
    intro i
    exact ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) lam).const_mul b).indicator measurableSet_Ioi
  have hint : ∀ i∈C, (∫ t in Ioi lam, term i t)=exp (-b*x i) := by
    intro i hiC
    change (∫ t in Ioi lam, (Ioi (x i)).indicator (fun t => b*exp (-b*t)) t)=_
    rw [setIntegral_indicator measurableSet_Ioi,Ioi_inter_Ioi,max_eq_right (hmin i hiC),
      integral_const_mul,integral_exp_mul_Ioi (neg_neg_of_pos hb)]
    field_simp
  have hbound : ∀ t∈Ioi lam, (∑ i∈C, term i t) ≤ b*exp (-(b-a)*t) := by
    intro t ht
    have hc : ((C.filter (fun i => x i<t)).card:ℝ) ≤ exp (a*t) := by
      apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hcount t ht.le)
      intro i hiC
      obtain ⟨hiC,hx⟩ := mem_filter.mp hiC
      exact mem_filter.mpr ⟨hiC,hx.le⟩
    calc
      _ = ((C.filter (fun i => x i<t)).card:ℝ)*(b*exp (-b*t)) := by
        simp only [term,Set.indicator_apply,Set.mem_Ioi,← Finset.sum_filter,sum_const,nsmul_eq_mul]
      _ ≤ exp (a*t)*(b*exp (-b*t)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by rw [mul_left_comm,← exp_add]; congr 2; ring
  have hbneg : -(b-a) < 0 := by linarith
  have hm := setIntegral_mono_on (integrable_finsetSum C (fun i _ => hi i))
    ((integrableOn_exp_mul_Ioi hbneg lam).const_mul b) measurableSet_Ioi hbound
  rw [integral_finsetSum C (fun i _ => hi i)] at hm
  have hsum : (∑ i∈C, ∫ t in Ioi lam, term i t)=∑ i∈C, exp (-b*x i) :=
    sum_congr rfl hint
  rw [hsum] at hm
  rw [integral_const_mul,integral_exp_mul_Ioi hbneg] at hm
  convert hm using 1 <;> field_simp <;> ring

end
end Cycle13
