import Cycle12.BernoulliConditioning
import Cycle12.FixedIntersectionConditioning

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem bernoulli_expect_powerset_formula (D : Finset V) (p : unitInterval)
    (f : Finset V → ℝ) :
    (subsetBernoulli D p).expect f=
      ∑ S∈D.powerset, (p:ℝ)^S.card*(1-(p:ℝ))^(D.card-S.card)*f S := by
  rw [subsetBernoulli_expect]
  apply sum_congr rfl
  intro S hS
  rw [subsetBernoulli_mass D S p (mem_powerset.mp hS)]

def binomialSizeMass (n : ℕ) (p : unitInterval) (j : ℕ) : ℝ :=
  (n.choose j:ℝ)*(p:ℝ)^j*(1-(p:ℝ))^(n-j)

theorem binomial_size_mass_nonneg (n : ℕ) (p : unitInterval) (j : ℕ) :
    0≤binomialSizeMass n p j := by
  unfold binomialSizeMass
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p.2.1 _))
    (pow_nonneg (sub_nonneg.mpr p.2.2) _)

/-- Exact decomposition of a Bernoulli sample by its cardinality. -/
theorem bernoulli_fixed_size_mixture (D : Finset V) (p : unitInterval)
    (f : Finset V → ℝ) :
    (subsetBernoulli D p).expect f=
      ∑ j ∈ range (D.card+1), binomialSizeMass D.card p j*(fixedSizeLaw D j).expect f := by
  rw [bernoulli_expect_powerset_formula,sum_powerset]
  apply sum_congr rfl
  intro j hj
  have hjD : j≤D.card := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [fixed_size_expect D hjD]
  have hc : (D.card.choose j:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hjD).ne'
  have he : (∑ S ∈ D.powersetCard j, (p:ℝ)^S.card*(1-(p:ℝ))^(D.card-S.card)*f S)=
      (p:ℝ)^j*(1-(p:ℝ))^(D.card-j)*(∑ S ∈ D.powersetCard j, f S) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [(mem_powersetCard.mp hS).2]
  rw [he]
  unfold binomialSizeMass
  field_simp

theorem bernoulli_size_probability (D : Finset V) (p : unitInterval) {j : ℕ} (hj : j≤D.card) :
    (subsetBernoulli D p).prob (fun S => S.card=j)=binomialSizeMass D.card p j := by
  rw [FiniteLaw.prob,bernoulli_expect_powerset_formula]
  calc
    _ = ∑ S ∈ D.powersetCard j, (p:ℝ)^S.card*(1-(p:ℝ))^(D.card-S.card) := by
      rw [powersetCard_eq_filter,sum_filter]
      apply sum_congr rfl
      intro S _
      split_ifs <;> simp
    _ = _ := by
      have hh := sum_powersetCard j D (fun l => (p:ℝ)^l*(1-(p:ℝ))^(D.card-l))
      simpa only [nsmul_eq_mul,binomialSizeMass,mul_assoc] using hh

end
end Cycle12
