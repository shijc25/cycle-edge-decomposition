import Cycle12.SubsetThreeVote
import Cycle12.FixedAdaptiveSubsample
import Cycle12.FixedSampleMean

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Two available votes are resolved by selecting one uniformly, which
has exactly the same color distribution as a fair tie coin. -/
def majorityVoteSize (j : ℕ) : ℕ := if j=0 then 0 else if j<3 then 1 else 3

theorem majority_vote_size_le (j : ℕ) : majorityVoteSize j ≤ j := by
  unfold majorityVoteSize
  split_ifs <;> omega

theorem majority_vote_size_cases (j : ℕ) :
    majorityVoteSize j=0 ∨ majorityVoteSize j=1 ∨ majorityVoteSize j=3 := by
  unfold majorityVoteSize
  split_ifs <;> simp

variable {V : Type} [Fintype V] [DecidableEq V]

def subsetVoteLaw (N : Finset V) : FiniteLaw (Finset V) :=
  fixedSizeLaw N (majorityVoteSize N.card)

def subsetMajority (B S : Finset V) : Prop := S.card<2*(S∩B).card

theorem subset_vote_support (N S : Finset V) (hS : 0<(subsetVoteLaw N).mass S) :
    S⊆N ∧ S.card=majorityVoteSize N.card :=
  fixed_size_support N S (majority_vote_size_le N.card) hS

theorem fixed_zero_expect (D : Finset V) (f : Finset V → ℝ) :
    (fixedSizeLaw D 0).expect f=f ∅ := by
  rw [fixed_size_expect D (Nat.zero_le _)]
  simp

theorem zero_subset_majority (D B : Finset V) :
    (fixedSizeLaw D 0).prob (subsetMajority B)=0 := by
  rw [FiniteLaw.prob,fixed_zero_expect]
  simp [subsetMajority]

theorem one_subset_majority (D B : Finset V) (hD : 1 ≤ D.card) (hB : B⊆D) :
    (fixedSizeLaw D 1).prob (subsetMajority B)=(B.card:ℝ)/D.card := by
  have he : (fixedSizeLaw D 1).prob (subsetMajority B)=
      (fixedSizeLaw D 1).expect (fun S => ((S∩B).card:ℝ)) := by
    apply finite_expect_congr_support
    intro S hS
    have hc := (fixed_size_support D S hD hS).2
    have hb : (S∩B).card ≤ 1 := by
      rw [← hc]
      exact card_le_card inter_subset_left
    unfold subsetMajority
    rw [hc]
    interval_cases h : (S∩B).card <;> norm_num
  rw [he,fixed_sample_count_mean D B hB hD]
  simp

theorem three_subset_majority (D B : Finset V) (hD : 3 ≤ D.card) :
    (fixedSizeLaw D 3).prob (subsetMajority B)=
      (fixedSizeLaw D 3).prob (fun S => 2 ≤ (S∩B).card) := by
  apply finite_expect_congr_support
  intro S hS
  have hc := (fixed_size_support D S hD hS).2
  unfold subsetMajority
  rw [hc]
  split_ifs <;> norm_num <;> omega

theorem subset_majority_adaptive_probability (D B : Finset V) (hD : 3 ≤ D.card)
    (hB : B⊆D) (j : ℕ) :
    (fixedSizeLaw D (majorityVoteSize j)).prob (subsetMajority B)=
      if j=0 then 0 else if j<3 then (B.card:ℝ)/D.card else
        (fixedSizeLaw D 3).prob (subsetMajority B) := by
  unfold majorityVoteSize
  split_ifs with hz hj
  · exact zero_subset_majority D B
  · exact one_subset_majority D B (by omega) hB
  · rfl

end
end Cycle12
