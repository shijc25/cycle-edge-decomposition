import Cycle12.FixedBinomialMixture
import Cycle12.FixedSizeMonotone

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem bernoulli_card_cdf (D : Finset V) (p : unitInterval) (k : ℕ) :
    (subsetBernoulli D p).prob (fun S => S.card≤k)=
      ∑ j∈range (D.card+1), binomialSizeMass D.card p j*(if j≤k then (1:ℝ) else 0) := by
  rw [FiniteLaw.prob,bernoulli_fixed_size_mixture]
  apply sum_congr rfl
  intro j hj
  congr 1
  calc
    _ = (fixedSizeLaw D j).prob (fun S => S.card≤k) := by
      unfold FiniteLaw.prob
      congr 1
    _ = _ := fixed_size_card_le_probability D (Nat.le_of_lt_succ (mem_range.mp hj)) k

/-- Exact decreasing-event transfer. The binomial mass below k is kept
explicit here; a factor-two corollary needs the integer-mean median theorem. -/
theorem bernoulli_to_fixed_decreasing_weighted (D : Finset V) (p : unitInterval)
    {k : ℕ} (hk : k≤D.card) (E : Finset V → Prop)
    (hE : ∀ S T, S⊆T → E T → E S) :
    (subsetBernoulli D p).prob (fun S => S.card≤k)*(fixedSizeLaw D k).prob E ≤
      (subsetBernoulli D p).prob E := by
  rw [bernoulli_card_cdf,sum_mul]
  conv_rhs => rw [FiniteLaw.prob,bernoulli_fixed_size_mixture]
  apply sum_le_sum
  intro j hj
  change binomialSizeMass D.card p j*(if j≤k then (1:ℝ) else 0)*(fixedSizeLaw D k).prob E ≤
    binomialSizeMass D.card p j*(fixedSizeLaw D j).prob E
  by_cases hjk : j≤k
  · rw [if_pos hjk,mul_one]
    exact mul_le_mul_of_nonneg_left (fixed_size_probability_antitone D hk hjk E hE)
      (binomial_size_mass_nonneg _ _ _)
  · rw [if_neg hjk,mul_zero,zero_mul]
    exact mul_nonneg (binomial_size_mass_nonneg _ _ _) (FiniteLaw.prob_nonneg _ _)

end
end Cycle12
