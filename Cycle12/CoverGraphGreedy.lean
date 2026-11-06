import Cycle12.Foundations.GreedyCycleBounds
import Cycle12.CoverBudgetBounds
import Cycle12.CoverDeleteAssembly

namespace Cycle12
open SimpleGraph Finset Real Cycle13 Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cover_nontrivial_graph (G : SimpleGraph V)
    (hF : coverGraphBudget (Fintype.card V) G.edgeSet.ncard < G.edgeSet.ncard) :
    (0:ℝ) < Fintype.card V ∧ (0:ℝ) < G.edgeSet.ncard ∧
      coverSampleV (coverGraphX (Fintype.card V) G.edgeSet.ncard) < 1 ∧
      (100:ℝ) < Fintype.card V ∧
      (43/10)*(Fintype.card V:ℝ)*cubeScale G.edgeSet.ncard ≤ G.edgeSet.ncard := by
  have hn₀ := Nat.cast_nonneg (α:=ℝ) (Fintype.card V)
  have hm₀ := Nat.cast_nonneg (α:=ℝ) G.edgeSet.ncard
  have hm := (cover_graph_budget_nonneg hn₀ hm₀).trans_lt hF
  have hsize : 2*(G.edgeSet.ncard:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
    simpa only [Set.fintypeCard_eq_ncard] using twice_graph_edges_le_order_sq G
  have hn : (0:ℝ) < Fintype.card V := by nlinarith only [hn₀,hm,hsize]
  have hid := cover_graph_budget_identity hn.le hm
  have hid' : coverSampleV (coverGraphX (Fintype.card V) G.edgeSet.ncard)*(G.edgeSet.ncard:ℝ)=coverGraphBudget (Fintype.card V) G.edgeSet.ncard := by
    rw [← hid]; exact div_mul_cancel₀ _ hm.ne'
  have hv : coverSampleV (coverGraphX (Fintype.card V) G.edgeSet.ncard) < 1 := by
    nlinarith only [hid',hF,hm]
  have hlarge := cover_nontrivial_order hn hm hsize hv
  have hFA : (0:ℝ) ≤ 3*(Fintype.card V:ℝ)*sqrt (Fintype.card V) := by positivity
  unfold coverGraphBudget at hF
  exact ⟨hn,hm,hv,hlarge,by linarith only [hF,hFA]⟩

/-- The entire x>=(17/250) branch, using the sharp long-cycle theorem and
proved logarithmic inequality. Its additive constants are exactly +2n,+n. -/
theorem cover_greedy (G : SimpleGraph V)
    (hF : coverGraphBudget (Fintype.card V) G.edgeSet.ncard < G.edgeSet.ncard)
    (hx : (17/250) ≤ coverGraphX (Fintype.card V) G.edgeSet.ncard) :
    FineCover G 2 ∧ CoarseCover G 1 := by
  obtain ⟨hn,hm,hv,hnlarge,_⟩ := cover_nontrivial_graph G hF
  have hn₃ : 3 ≤ Fintype.card V := by exact_mod_cast (show (3:ℝ) ≤ Fintype.card V by linarith)
  have hsize : 2*(G.edgeSet.ncard:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
    simpa only [Set.fintypeCard_eq_ncard] using twice_graph_edges_le_order_sq G
  obtain ⟨P,hPc,hPe⟩ := exists_greedy_real_budget G hn₃
    (cover_cycle_budget_nonneg hn.le hm.le)
  obtain ⟨Q,hQc,hQe⟩ := exists_greedy_half_budget G hn₃
  have hPf := cover_greedy_fine_budget hn hm hsize hx hv
  have hQf := cover_greedy_coarse_budget hn hm hx hv
  refine ⟨⟨P,hPc,?_⟩,⟨Q,hQc,?_⟩⟩
  · linarith only [hPe,hPf]
  · simp only [one_mul]
    linarith only [hQe,hQf]

end
end Cycle12
