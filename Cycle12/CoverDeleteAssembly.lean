import Cycle12.CoverCutAssembly
import Cycle12.Foundations.MixedCoverDelete

namespace Cycle12
open SimpleGraph Finset Cycle13 Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fineCover_trivial (G : SimpleGraph V) {extra : ℝ} (ha : 0 ≤ extra)
    (hm : (G.edgeSet.ncard:ℝ) ≤ coverGraphBudget (Fintype.card V) G.edgeSet.ncard) :
    FineCover G extra := by
  refine ⟨CyclePacking.empty G,?_,?_⟩
  · simp only [CyclePacking.empty,Nat.cast_zero]
    exact cover_cycle_budget_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [CyclePacking.singles_empty]
    linarith [mul_nonneg ha (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))]

theorem coarseCover_trivial (G : SimpleGraph V) {extra : ℝ} (ha : 0 ≤ extra)
    (hm : (G.edgeSet.ncard:ℝ) ≤ coverGraphBudget (Fintype.card V) G.edgeSet.ncard) :
    CoarseCover G extra := by
  refine ⟨CyclePacking.empty G,?_,?_⟩
  · simp only [CyclePacking.empty,Nat.cast_zero]
    positivity
  · rw [CyclePacking.singles_empty]
    linarith [mul_nonneg ha (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))]

theorem fineCover_delete (G : SimpleGraph V) (v : V) {extra : ℝ}
    (ha : 0 ≤ extra) (hn : 1 < Fintype.card V)
    (hIH : FineCover (G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)) extra)
    (hpay : coverGraphBudget (Fintype.card V-1) ((G.edgeSet.ncard:ℝ)-G.degree v)+G.degree v ≤
      coverGraphBudget (Fintype.card V) G.edgeSet.ncard) : FineCover G extra := by
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
    exact hPc.trans ((cover_cycle_budget_mono_order (by linarith : (0:ℝ) < (Fintype.card V:ℝ)-1)
      (by linarith)).trans (cover_cycle_budget_mono_edges (Nat.cast_nonneg _) hmR
      (sub_le_self _ (Nat.cast_nonneg _))))
  · rw [he,Nat.cast_add]
    linarith only [hPe,hpay,ha]

theorem coarseCover_delete (G : SimpleGraph V) (v : V) {extra : ℝ}
    (ha : 0 ≤ extra)
    (hIH : CoarseCover (G.induce ((({v}:Finset V)ᶜ : Finset V):Set V)) extra)
    (hpay : coverGraphBudget (Fintype.card V-1) ((G.edgeSet.ncard:ℝ)-G.degree v)+G.degree v ≤
      coverGraphBudget (Fintype.card V) G.edgeSet.ncard) : CoarseCover G extra := by
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
end Cycle12
