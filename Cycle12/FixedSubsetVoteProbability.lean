import Cycle12.SubsetVoteRule
import Cycle12.FixedSamplePoissonTail

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

theorem finite_expect_binary_mixture {Ω : Type} [Fintype Ω] (mu : FiniteLaw Ω)
    (E : Ω → Prop) (a b : ℝ) :
    mu.expect (fun x => if E x then a else b)=mu.prob E*a+(1-mu.prob E)*b := by
  calc
    _ = mu.expect (fun x => b+(a-b)*(if E x then 1 else 0)) := by
      congr 1
      funext x
      split_ifs <;> ring
    _ = b+(a-b)*mu.prob E := by
      rw [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_const_mul]
      rfl
    _ = _ := by ring

variable {V : Type} [Fintype V] [DecidableEq V]

def lowPositiveVoteProbability (D N : Finset V) (k : ℕ) : ℝ :=
  (fixedSizeLaw D k).prob (fun T => 0<(T∩N).card ∧ (T∩N).card<3)

theorem fixed_subset_vote_majority_mean (D N B : Finset V) (hN : N⊆D)
    (hB : B⊆N) (hN3 : 3 ≤ N.card) {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).expect (fun T => (subsetVoteLaw (T∩N)).prob (subsetMajority B)) ≤
      lowPositiveVoteProbability D N k*((B.card:ℝ)/N.card)+
        (1-lowPositiveVoteProbability D N k)*majorityCorrection N.card*
          majorityPolynomial ((B.card:ℝ)/N.card) := by
  have he : (fixedSizeLaw D k).expect (fun T => (subsetVoteLaw (T∩N)).prob (subsetMajority B))=
      (fixedSizeLaw D k).expect (fun T =>
        (fixedSizeLaw N (majorityVoteSize (T∩N).card)).prob (subsetMajority B)) := by
    exact fixed_intersection_adaptive_subsample D N hN hk majorityVoteSize majority_vote_size_le
      (fun S => if subsetMajority B S then 1 else 0)
  rw [he]
  simp_rw [subset_majority_adaptive_probability N B hN3 hB]
  have hm : 0 ≤ (fixedSizeLaw N 3).prob (subsetMajority B) := FiniteLaw.prob_nonneg _ _
  calc
    _ ≤ (fixedSizeLaw D k).expect (fun T =>
        if 0<(T∩N).card ∧ (T∩N).card<3 then (B.card:ℝ)/N.card
        else (fixedSizeLaw N 3).prob (subsetMajority B)) := by
      apply FiniteLaw.expect_mono
      intro T
      by_cases hz : (T∩N).card=0
      · simpa only [hz,ite_true,lt_self_iff_false,false_and,ite_false] using hm
      · have hpos : 0<(T∩N).card := by omega
        simp [hz,hpos]
    _ = lowPositiveVoteProbability D N k*((B.card:ℝ)/N.card)+
        (1-lowPositiveVoteProbability D N k)*(fixedSizeLaw N 3).prob (subsetMajority B) := by
      have hh := finite_expect_binary_mixture (fixedSizeLaw D k)
        (fun T => 0<(T∩N).card ∧ (T∩N).card<3)
        ((B.card:ℝ)/N.card) ((fixedSizeLaw N 3).prob (subsetMajority B))
      convert hh using 1
      · congr 1
        funext T
        split_ifs <;> rfl
      · rfl
    _ ≤ _ := by
      have hbound := three_subset_majority_bound N B hN3 hB
      rw [← three_subset_majority N B hN3] at hbound
      have ha : 0 ≤ 1-lowPositiveVoteProbability D N k :=
        sub_nonneg.mpr (FiniteLaw.prob_le_one _ _)
      have hh := mul_le_mul_of_nonneg_left hbound ha
      linarith only [hh]

theorem low_positive_vote_nonneg (D N : Finset V) (k : ℕ) :
    0 ≤ lowPositiveVoteProbability D N k := FiniteLaw.prob_nonneg _ _

theorem low_positive_vote_poisson (D N : Finset V) (hN : N⊆D)
    {k : ℕ} (hk : k ≤ D.card) {lambda : ℝ} (hlambda : 3 ≤ lambda)
    (hmean : lambda ≤ (k:ℝ)*N.card/D.card) :
    lowPositiveVoteProbability D N k ≤ min 1 (poissonTailTwo lambda) := by
  exact (FiniteLaw.prob_mono _ (fun _ h => h.2)).trans
    (fixed_sample_low_vote_poisson_capped D N hN hk hlambda hmean)

end
end Cycle12
