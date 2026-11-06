import Cycle12.Foundations.FiniteLaw
import Mathlib.Probability.Distributions.SetBernoulli

/-! The explicit finite Bernoulli subset law and its exact polynomial
generating function. These weights agree with mathlib's setBernoulli. -/
namespace Cycle13
open Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def bernoulliSubset (p : unitInterval) : FiniteLaw (Finset V) where
  mass S := (p:ℝ)^S.card*(1-(p:ℝ))^(Fintype.card V-S.card)
  nonneg S := mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (by linarith [p.2.2]) _)
  total := by rw [Fintype.sum_pow_mul_eq_add_pow]; simp

theorem bernoulliSubset_generating (p : unitInterval) (z : ℝ) :
    (bernoulliSubset (V:=V) p).expect (fun S => z^S.card)=(1-(p:ℝ)+(p:ℝ)*z)^Fintype.card V := by
  unfold FiniteLaw.expect bernoulliSubset
  have hp : ∀ S : Finset V,
      (p:ℝ)^S.card*(1-(p:ℝ))^(Fintype.card V-S.card)*z^S.card=
        ((p:ℝ)*z)^S.card*(1-(p:ℝ))^(Fintype.card V-S.card) := by
    intro S; rw [mul_pow]; ring
  simp_rw [hp]
  rw [Fintype.sum_pow_mul_eq_add_pow,add_comm]

theorem bernoulliSubset_exponential_generating (p : unitInterval) (a : ℝ) :
    (bernoulliSubset (V:=V) p).expect (fun S => exp (a*S.card))=
      (1-(p:ℝ)+(p:ℝ)*exp a)^Fintype.card V := by
  simp_rw [mul_comm a,Real.exp_nat_mul]
  exact bernoulliSubset_generating p (exp a)

theorem bernoulliSubset_generating_le_exp (p : unitInterval) {z : ℝ} (hz : 0 ≤ z) :
    (bernoulliSubset (V:=V) p).expect (fun S => z^S.card) ≤
      exp ((p:ℝ)*(z-1)*Fintype.card V) := by
  rw [bernoulliSubset_generating]
  have hn : 0 ≤ 1-(p:ℝ)+(p:ℝ)*z := by nlinarith [p.2.1,p.2.2]
  have he : 1-(p:ℝ)+(p:ℝ)*z ≤ exp ((p:ℝ)*(z-1)) := by
    have hh := Real.add_one_le_exp ((p:ℝ)*(z-1)); nlinarith
  have hh := pow_le_pow_left₀ hn he (Fintype.card V)
  rw [← Real.exp_nat_mul] at hh
  simpa only [mul_comm (Fintype.card V:ℝ)] using hh

theorem bernoulliSubset_mass_eq_setBernoulli (p : unitInterval) (S : Finset V) :
    (bernoulliSubset p).mass S=(setBernoulli (Set.univ : Set V) p).real {(S : Set V)} := by
  rw [setBernoulli_real_singleton p (Set.subset_univ _) (Set.toFinite _)]
  rw [Set.ncard_sdiff' (Set.subset_univ (S:Set V)) (Set.toFinite _)]
  simp only [bernoulliSubset,Set.ncard_coe_finset,Set.ncard_univ,Nat.card_eq_fintype_card]

theorem label_weight_sum (T : Finset V) (z : ℝ) :
    (∑ A∈T.powerset, z^A.card)=(1+z)^T.card := by
  have hh := Finset.sum_pow_mul_eq_add_pow z (1:ℝ) T
  simpa only [one_pow,mul_one,add_comm z 1] using hh

theorem label_exponential_sum (T : Finset V) (a : ℝ) :
    (∑ A∈T.powerset, exp (a*A.card))=(1+exp a)^T.card := by
  simp_rw [mul_comm a,Real.exp_nat_mul]
  exact label_weight_sum T (exp a)

theorem label_entropy_expectation (p : unitInterval) (a : ℝ) :
    (bernoulliSubset (V:=V) p).expect
      (fun T => ∑ A∈T.powerset, exp (a*A.card)) ≤ exp ((p:ℝ)*exp a*Fintype.card V) := by
  simp_rw [label_exponential_sum]
  have hh := bernoulliSubset_generating_le_exp (V:=V) p
    (z:=1+exp a) (by positivity)
  convert hh using 1 <;> congr 1 <;> ring

end
end Cycle13
