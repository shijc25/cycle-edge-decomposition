import Cycle12.OriginalMatchingGroups12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 600000

/-- Both pairing passes followed by even grouping of the actual retained
matching. The ledger covers the original crossing class exactly. -/
theorem prepare_crossing_with_groups (G : SimpleGraph V) (U T : Finset V)
    (hUT : Disjoint U T)
    (hcross : ∀ {x y},G.Adj x y → (x∈U ∧ y∈T) ∨ (x∈T ∧ y∈U))
    {Q : ℕ} (hQ : 0<Q) :
    ∃ (P : CenterPairings G U) (S : CenterPairings P.residue Uᶜ)
      (M : (⊤ : SimpleGraph S.residue.edgeSet).Subgraph),
      (∀ e : P.Index,P.left e∈U ∧ P.right e∈U) ∧
      (∀ e : S.Index,S.left e∈T ∧ S.right e∈T) ∧
      (∀ v,S.residue.degree v ≤ 1) ∧ M.IsMatching ∧
      (matchingRetainedGraph S.residue M) ≤ G ∧
      (matchingRetainedGraph S.residue M).edgeSet.ncard ≤ 1 ∧
      Disjoint P.used S.used ∧
      (∀ t,Disjoint P.used (matchingOriginalGroup S.residue M Q t)) ∧
      (∀ t,Disjoint S.used (matchingOriginalGroup S.residue M Q t)) ∧
      Disjoint P.used (matchingRetainedGraph S.residue M).edgeSet ∧
      Disjoint S.used (matchingRetainedGraph S.residue M).edgeSet ∧
      (∀ t,Disjoint (matchingOriginalGroup S.residue M Q t)
        (matchingRetainedGraph S.residue M).edgeSet) ∧
      Pairwise (fun t u => Disjoint (matchingOriginalGroup S.residue M Q t)
        (matchingOriginalGroup S.residue M Q u)) ∧
      P.used∪S.used∪(⋃ t,matchingOriginalGroup S.residue M Q t)∪
        (matchingRetainedGraph S.residue M).edgeSet=G.edgeSet ∧
      (∀ t,Even (matchingOriginalGroup S.residue M Q t).ncard ∧
        (matchingOriginalGroup S.residue M Q t).ncard ≤ 2*Q) ∧
      (Fintype.card (Fin (Fintype.card M.edgeSet/Q+1)):ℝ) ≤
        (S.residue.edgeSet.ncard:ℝ)/(2*Q)+1 := by
  obtain ⟨P,S,hP,hS,hdegree,hPS,hPR,hSR,hcover,hcard⟩ := prepare_two_blocks G U T hUT hcross
  obtain ⟨M,hM,hsub,hremain,hgroupSub,hgroupRem,hdisj,hgroupCover,hgroupCard,hgroupCount⟩ :=
    original_matching_group_partition S.residue hQ
  have hRG : S.residue ≤ G := fun _ _ h => h.1.1
  have hret := edgeSet_mono hsub
  refine ⟨P,S,M,hP,hS,hdegree,hM,hsub.trans hRG,hremain,hPS,?_,?_,
    hPR.mono_right hret,hSR.mono_right hret,hgroupRem,hdisj,?_,hgroupCard,hgroupCount⟩
  · intro t
    exact hPR.mono_right (hgroupSub t)
  · intro t
    exact hSR.mono_right (hgroupSub t)
  · rw [Set.union_assoc,hgroupCover]
    exact hcover

end
end Cycle12
