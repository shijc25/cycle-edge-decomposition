import Cycle12.Foundations.MixedCoverCut
import Cycle12.Foundations.MixedDeleteBudget

namespace Cycle13
open SimpleGraph Finset MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem CyclePacking.singles_empty (G : SimpleGraph V) : (CyclePacking.empty G).singles=G.edgeSet.ncard := by
  simp [CyclePacking.singles,CyclePacking.residue,CyclePacking.used,CyclePacking.empty]

theorem fineMixedCover_trivial (G : SimpleGraph V) {extra : ℝ} (ha : 0 ≤ extra)
    (hm : (G.edgeSet.ncard:ℝ) ≤ mixedBudget (Fintype.card V) G.edgeSet.ncard) :
    FineMixedCover G extra := by
  refine ⟨CyclePacking.empty G,?_,?_⟩
  · simp only [CyclePacking.empty,Nat.cast_zero]
    exact cycleBudget_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [CyclePacking.singles_empty]
    linarith [mul_nonneg ha (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))]

theorem coarseMixedCover_trivial (G : SimpleGraph V) {extra : ℝ} (ha : 0 ≤ extra)
    (hm : (G.edgeSet.ncard:ℝ) ≤ mixedBudget (Fintype.card V) G.edgeSet.ncard) :
    CoarseMixedCover G extra := by
  refine ⟨CyclePacking.empty G,?_,?_⟩
  · simp only [CyclePacking.empty,Nat.cast_zero]
    positivity
  · rw [CyclePacking.singles_empty]
    linarith [mul_nonneg ha (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))]

theorem induce_singleton_eq_bot (G : SimpleGraph V) (v : V) :
    G.induce (({v}:Finset V):Set V)=⊥ := by
  ext x y
  change G.Adj x.val y.val ↔ False
  have hx : x.val=v := mem_singleton.mp x.property
  have hy : y.val=v := mem_singleton.mp y.property
  simp [hx,hy]

theorem delete_vertex_order (v : V) :
    Fintype.card ((({v}:Finset V)ᶜ : Finset V):Set V)+1=Fintype.card V := by
  have hc : Fintype.card ((({v}:Finset V)ᶜ : Finset V):Set V)=(({v}:Finset V)ᶜ).card :=
    Fintype.card_of_finset' _ (by simp)
  rw [hc]
  have hh := card_add_card_compl ({v}:Finset V)
  simp only [card_singleton] at hh
  omega

theorem delete_vertex_edges (G : SimpleGraph V) (v : V) :
    (G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)).edgeSet.ncard+G.degree v=G.edgeSet.ncard := by
  have hh := induced_cut_edge_partition G ({v}:Finset V)
  rw [induce_singleton_eq_bot,edgeSet_bot,Set.ncard_empty,zero_add,cutSize_singleton] at hh
  exact hh

theorem exists_packing_delete_vertex (G : SimpleGraph V) (v : V)
    (P : CyclePacking (G.induce ((({v}:Finset V)ᶜ : Finset V):Set V))) :
    ∃ C : CyclePacking G, C.count=P.count ∧ C.singles=P.singles+G.degree v := by
  obtain ⟨C,hc,he⟩ := exists_packing_across_cut G ({v}:Finset V)
    (CyclePacking.empty _) P
  have hzero : (CyclePacking.empty (G.induce (({v}:Finset V):Set V))).singles=0 := by
    rw [CyclePacking.singles_empty,induce_singleton_eq_bot,edgeSet_bot,Set.ncard_empty]
  refine ⟨C,?_,?_⟩
  · simpa only [CyclePacking.empty,zero_add] using hc
  · simpa only [hzero,zero_add,cutSize_singleton] using he

theorem fineMixedCover_delete (G : SimpleGraph V) (v : V) {extra : ℝ}
    (ha : 0 ≤ extra) (hn : 1 < Fintype.card V)
    (hIH : FineMixedCover (G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)) extra)
    (hpay : mixedBudget (Fintype.card V-1) ((G.edgeSet.ncard:ℝ)-G.degree v)+G.degree v ≤
      mixedBudget (Fintype.card V) G.edgeSet.ncard) : FineMixedCover G extra := by
  obtain ⟨P,hPc,hPe⟩ := hIH
  obtain ⟨C,hc,he⟩ := exists_packing_delete_vertex G v P
  have horder := delete_vertex_order v
  have hedges := delete_vertex_edges G v
  have hnr : (Fintype.card ((({v}:Finset V)ᶜ : Finset V):Set V):ℝ)=(Fintype.card V:ℝ)-1 := by
    have hh : (Fintype.card ((({v}:Finset V)ᶜ : Finset V):Set V):ℝ)+1=Fintype.card V := by exact_mod_cast horder
    linarith
  have hmr : ((G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)).edgeSet.ncard:ℝ)=
      (G.edgeSet.ncard:ℝ)-G.degree v := by
    have hh : ((G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)).edgeSet.ncard:ℝ)+G.degree v=G.edgeSet.ncard := by exact_mod_cast hedges
    linarith
  rw [hnr,hmr] at hPc hPe
  refine ⟨C,?_,?_⟩
  · rw [hc]
    have hnR : (1:ℝ) < Fintype.card V := by exact_mod_cast hn
    have hmR : (0:ℝ) ≤ (G.edgeSet.ncard:ℝ)-G.degree v := by rw [← hmr]; positivity
    exact hPc.trans ((cycleBudget_mono_order (by linarith : (0:ℝ) < (Fintype.card V:ℝ)-1)
      (by linarith)).trans (cycleBudget_mono_edges (Nat.cast_nonneg _) hmR
      (sub_le_self _ (Nat.cast_nonneg _))))
  · rw [he,Nat.cast_add]
    linarith only [hPe,hpay,ha]

theorem coarseMixedCover_delete (G : SimpleGraph V) (v : V) {extra : ℝ}
    (ha : 0 ≤ extra)
    (hIH : CoarseMixedCover (G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)) extra)
    (hpay : mixedBudget (Fintype.card V-1) ((G.edgeSet.ncard:ℝ)-G.degree v)+G.degree v ≤
      mixedBudget (Fintype.card V) G.edgeSet.ncard) : CoarseMixedCover G extra := by
  obtain ⟨P,hPc,hPe⟩ := hIH
  obtain ⟨C,hc,he⟩ := exists_packing_delete_vertex G v P
  have hn : (Fintype.card ((({v}:Finset V)ᶜ : Finset V):Set V):ℝ)+1=Fintype.card V := by
    exact_mod_cast delete_vertex_order v
  have hm : ((G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)).edgeSet.ncard:ℝ)+G.degree v=G.edgeSet.ncard := by
    exact_mod_cast delete_vertex_edges G v
  have hnr : (Fintype.card ((({v}:Finset V)ᶜ : Finset V):Set V):ℝ)=(Fintype.card V:ℝ)-1 := by linarith
  have hmr : ((G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)).edgeSet.ncard:ℝ)=
      (G.edgeSet.ncard:ℝ)-G.degree v := by linarith
  rw [hnr,hmr] at hPe
  refine ⟨C,?_,?_⟩
  · rw [hc]
    linarith only [hPc,hn]
  · rw [he,Nat.cast_add]
    linarith only [hPe,hpay,ha]

end
end Cycle13
