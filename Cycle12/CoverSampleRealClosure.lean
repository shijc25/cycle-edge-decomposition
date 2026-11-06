import Cycle12.CoverSampleClosure

namespace Cycle12
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cover_of_sample_cycles_real (G : SimpleGraph V) (U : Finset V) (C : CyclePacking G)
    (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hxmax : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ 17/250)
    (hcard : U.card=⌊coverSampleP (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*(Fintype.card V:ℝ)⌋₊)
    (hcount : (C.count:ℝ) ≤ ((Fintype.card V:ℝ)-U.card)/2)
    (hsingles : (C.singles:ℝ) ≤ coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet)+
      (Fintype.card V:ℝ)-U.card) : FineCover G 2 ∧ CoarseCover G 1 := by
  have hsize := twice_graph_edges_le_order_sq G
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  have hbudget := cover_sample_count_within_cycle_budget (count:=(C.count:ℝ)) hn hm hsize hxmax
    (by rwa [hcard] at hcount)
  have hsingle : (C.singles:ℝ) ≤ coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet)+(Fintype.card V:ℝ) :=
    hsingles.trans (sub_le_self _ (Nat.cast_nonneg _))
  have hhalf : (C.count:ℝ) ≤ (Fintype.card V:ℝ)/2 := by linarith [Nat.cast_nonneg (α:=ℝ) U.card]
  simp only [Set.fintypeCard_eq_ncard] at hbudget hsingle
  exact ⟨⟨C,hbudget,by linarith only [hsingle,hn]⟩,⟨C,hhalf,by simpa only [one_mul] using hsingle⟩⟩

end
end Cycle12
