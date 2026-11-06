import Cycle12.Foundations.PackingCut
import Cycle12.CoverCycleBudget

namespace Cycle12
open SimpleGraph Finset Cycle13 Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def FineCover (G : SimpleGraph V) (extra : ℝ) : Prop :=
  ∃ P : CyclePacking G,
    (P.count:ℝ) ≤ coverCycleBudget (Fintype.card V) G.edgeSet.ncard ∧
    (P.singles:ℝ) ≤ coverGraphBudget (Fintype.card V) G.edgeSet.ncard+extra*Fintype.card V

def CoarseCover (G : SimpleGraph V) (extra : ℝ) : Prop :=
  ∃ P : CyclePacking G,
    (P.count:ℝ) ≤ (Fintype.card V:ℝ)/2 ∧
    (P.singles:ℝ) ≤ coverGraphBudget (Fintype.card V) G.edgeSet.ncard+extra*Fintype.card V

theorem cover_induced_orders_add (S : Finset V) :
    Fintype.card ↥S+Fintype.card ↥(Sᶜ : Finset V)=Fintype.card V := by
  simpa only [Fintype.card_coe] using card_add_card_compl S

/-- Fine cycle counts and residual-edge budgets both survive a sparse-cut
split. The cycles are explicitly embedded and assembled on the original graph. -/
theorem fineCover_cut (G : SimpleGraph V) (S : Finset V) {extra : ℝ}
    (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (h₁ : FineCover (G.induce (S:Set V)) extra)
    (h₂ : FineCover (G.induce ((Sᶜ : Finset V):Set V)) extra)
    (hpay : coverGraphBudget S.card (G.induce (S:Set V)).edgeSet.ncard+
      coverGraphBudget (Sᶜ : Finset V).card (G.induce ((Sᶜ : Finset V):Set V)).edgeSet.ncard+
      cutSize G S ≤ coverGraphBudget (Fintype.card V) G.edgeSet.ncard) :
    FineCover G extra := by
  obtain ⟨P,hP,hPe⟩ := h₁
  obtain ⟨Q,hQ,hQe⟩ := h₂
  obtain ⟨C,hcount,hsingle⟩ := exists_packing_across_cut G S P Q
  have hcard₁ : Fintype.card (S:Set V)=S.card := Fintype.card_of_finset' S (by simp)
  have hcard₂ : Fintype.card ((Sᶜ : Finset V):Set V)=(Sᶜ : Finset V).card :=
    Fintype.card_of_finset' (Sᶜ : Finset V) (by simp)
  rw [hcard₁] at hP hPe
  rw [hcard₂] at hQ hQe
  have hn : (S.card:ℝ)+(Sᶜ : Finset V).card=Fintype.card V := by
    exact_mod_cast card_add_card_compl S
  have he : ((G.induce (S:Set V)).edgeSet.ncard:ℝ)+
      (G.induce ((Sᶜ : Finset V):Set V)).edgeSet.ncard+(cutSize G S:ℝ)=G.edgeSet.ncard := by
    exact_mod_cast induced_cut_edge_partition G S
  refine ⟨C,?_,?_⟩
  · have hcycle := cover_cycle_budget_superadditive
      (n₁:=(S.card:ℝ)) (n₂:=((Sᶜ : Finset V).card:ℝ))
      (m₁:=(G.induce (S:Set V)).edgeSet.ncard)
      (m₂:=(G.induce ((Sᶜ : Finset V):Set V)).edgeSet.ncard)
      (by exact_mod_cast card_pos.mpr hS) (by exact_mod_cast card_pos.mpr hSc)
    rw [hn] at hcycle
    have hm := cover_cycle_budget_mono_edges (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
      (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (show ((G.induce (S:Set V)).edgeSet.ncard:ℝ)+
        (G.induce ((Sᶜ : Finset V):Set V)).edgeSet.ncard ≤ G.edgeSet.ncard by
        linarith [Nat.cast_nonneg (α:=ℝ) (cutSize G S)])
    rw [hcount,Nat.cast_add]
    linarith only [hP,hQ,hcycle,hm]
  · rw [hsingle,Nat.cast_add,Nat.cast_add]
    have hh : extra*S.card+extra*(Sᶜ : Finset V).card=extra*Fintype.card V := by
      rw [← mul_add,hn]
    linarith only [hPe,hQe,hpay,hh]

theorem coarseCover_cut (G : SimpleGraph V) (S : Finset V) {extra : ℝ}
    (h₁ : CoarseCover (G.induce (S:Set V)) extra)
    (h₂ : CoarseCover (G.induce ((Sᶜ : Finset V):Set V)) extra)
    (hpay : coverGraphBudget S.card (G.induce (S:Set V)).edgeSet.ncard+
      coverGraphBudget (Sᶜ : Finset V).card (G.induce ((Sᶜ : Finset V):Set V)).edgeSet.ncard+
      cutSize G S ≤ coverGraphBudget (Fintype.card V) G.edgeSet.ncard) :
    CoarseCover G extra := by
  obtain ⟨P,hP,hPe⟩ := h₁
  obtain ⟨Q,hQ,hQe⟩ := h₂
  obtain ⟨C,hcount,hsingle⟩ := exists_packing_across_cut G S P Q
  have hcard₁ : Fintype.card (S:Set V)=S.card := Fintype.card_of_finset' S (by simp)
  have hcard₂ : Fintype.card ((Sᶜ : Finset V):Set V)=(Sᶜ : Finset V).card :=
    Fintype.card_of_finset' (Sᶜ : Finset V) (by simp)
  rw [hcard₁] at hP hPe
  rw [hcard₂] at hQ hQe
  have hn : (S.card:ℝ)+(Sᶜ : Finset V).card=Fintype.card V := by
    exact_mod_cast card_add_card_compl S
  refine ⟨C,?_,?_⟩
  · rw [hcount,Nat.cast_add]
    linarith only [hP,hQ,hn]
  · rw [hsingle,Nat.cast_add,Nat.cast_add]
    have hh : extra*S.card+extra*(Sᶜ : Finset V).card=extra*Fintype.card V := by
      rw [← mul_add,hn]
    linarith only [hPe,hQe,hpay,hh]

end
end Cycle12
