import Cycle12.Foundations.SubsetBernoulliMGF

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_miss (W N : Finset V) (p : unitInterval) (hN : N⊆W) :
    (subsetBernoulli W p).prob (fun T => N∩T=∅)=(1-(p:ℝ))^N.card := by
  have hprod : ∀ T : Finset V, (∏ v∈T, if v∈N then (0:ℝ) else 1)=
      if N∩T=∅ then 1 else 0 := by
    intro T
    rw [prod_ite]
    simp only [prod_const,one_pow,mul_one,filter_mem_eq_inter]
    rw [inter_comm T N]
    by_cases h : N∩T=∅
    · simp [h]
    · have hc : (N∩T).card≠0 := card_ne_zero.mpr (nonempty_iff_ne_empty.mpr h)
      simp [h,hc]
  have hh := subsetBernoulli_expect_product W p (fun v => if v∈N then 0 else 1)
  simp_rw [hprod] at hh
  have he : ∀ v : V, 1-(p:ℝ)+(p:ℝ)*(if v∈N then 0 else 1)=
      if v∈N then 1-(p:ℝ) else 1 := by
    intro v; by_cases hv : v∈N <;> simp [hv]
  simp_rw [he] at hh
  rw [prod_ite] at hh
  simp only [prod_const,filter_mem_eq_inter,inter_eq_right.mpr hN,one_pow,mul_one] at hh
  rw [← hh,FiniteLaw.prob]
  congr 1
  funext T
  by_cases h : N∩T=∅ <;> simp [h]

theorem subsetBernoulli_miss_le (W N : Finset V) (p : unitInterval) (hN : N⊆W) :
    (subsetBernoulli W p).prob (fun T => N∩T=∅) ≤ exp (-(p:ℝ)*N.card) := by
  rw [subsetBernoulli_miss W N p hN]
  have hh : 1-(p:ℝ) ≤ exp (-(p:ℝ)) := by
    have he := Real.add_one_le_exp (-(p:ℝ)); linarith
  have hb := pow_le_pow_left₀ (sub_nonneg.mpr p.2.2) hh N.card
  rw [← Real.exp_nat_mul] at hb
  simpa only [mul_comm (N.card:ℝ)] using hb

end
end Cycle13
