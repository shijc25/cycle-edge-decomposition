import Cycle12.FixedSubsetVoteProbability

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem subset_vote_empty_probability (N : Finset V) :
    (subsetVoteLaw N).prob (fun S => S=∅)=if N=∅ then 1 else 0 := by
  rw [FiniteLaw.prob,← (subsetVoteLaw N).expect_const (if N=∅ then 1 else 0)]
  apply finite_expect_congr_support
  intro S hS
  obtain ⟨hSN,hcard⟩ := subset_vote_support N S hS
  by_cases hN : N=∅
  · have hS : S=∅ := subset_empty.mp (hN ▸ hSN)
    simp [hN,hS]
  · have hc : N.card≠0 := by simpa using hN
    have hS : S≠∅ := by
      intro hz
      rw [hz,card_empty] at hcard
      unfold majorityVoteSize at hcard
      split_ifs at hcard <;> omega
    simp [hN,hS]

def subsetCopiedError (T A : Finset V) (v : V) (S : Finset V) : Prop :=
  v∉T ∧ ¬(v∈A ↔ subsetMajority (A∩T) S)

/-- For an odd nonzero vote set, a wrong original color means a strict
majority of crossing neighbors. Only the original A side pays a zero vote. -/
theorem subset_vote_error_event (N T A S : Finset V) (v : V)
    (hS : 0<(subsetVoteLaw (T∩N)).mass S) (herr : subsetCopiedError T A v S) :
    subsetMajority (if v∈A then N\A else N∩A) S ∨ (v∈A ∧ S=∅) := by
  obtain ⟨hSTN,hcard⟩ := subset_vote_support (T∩N) S hS
  have hST : S⊆T := hSTN.trans inter_subset_left
  have hSN : S⊆N := hSTN.trans inter_subset_right
  have hi : S∩(A∩T)=S∩A := by
    ext w
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hST h.1⟩⟩
  obtain ⟨hvT,herr⟩ := herr
  by_cases hvA : v∈A
  · by_cases hz : S=∅
    · exact Or.inr ⟨hvA,hz⟩
    · left
      rw [if_pos hvA]
      have hs : S∩(N\A)=S\A := by
        ext w
        simp only [mem_inter,mem_sdiff]
        exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hSN h.1,h.2⟩⟩
      have hwrong : ¬subsetMajority (A∩T) S := by tauto
      unfold subsetMajority at hwrong ⊢
      rw [hi] at hwrong
      rw [hs]
      have hsum := card_sdiff_add_card_inter S A
      have hcases := majority_vote_size_cases (T∩N).card
      have hnonzero : S.card≠0 := by simpa using hz
      omega
  · left
    rw [if_neg hvA]
    have hs : S∩(N∩A)=S∩A := by
      ext w
      simp only [mem_inter]
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hSN h.1,h.2⟩⟩
    have hwrong : subsetMajority (A∩T) S := by tauto
    unfold subsetMajority at hwrong ⊢
    simpa only [hi,hs] using hwrong

theorem subset_vote_error_bound (N T A : Finset V) (v : V) :
    (subsetVoteLaw (T∩N)).prob (subsetCopiedError T A v) ≤
      (subsetVoteLaw (T∩N)).prob (subsetMajority (if v∈A then N\A else N∩A))+
        if v∈A then (if T∩N=∅ then 1 else 0) else 0 := by
  apply (FiniteLaw.prob_mono_support _ (fun S hS herr => subset_vote_error_event N T A S v hS herr)).trans
  have hh := (subsetVoteLaw (T∩N)).prob_union_le
    (subsetMajority (if v∈A then N\A else N∩A)) (fun S => v∈A ∧ S=∅)
  by_cases hv : v∈A
  · simpa only [hv,ite_true,true_and,subset_vote_empty_probability] using hh
  · simpa only [hv,ite_false,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const,add_zero] using hh

end
end Cycle12
