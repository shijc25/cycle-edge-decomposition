import Cycle12.CoverSampleDiscount
import Cycle12.CoverDeleteAssembly
import Cycle12.Foundations.SampledCyclePacking

namespace Cycle12
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Close the arithmetic of the actual outside-path construction, with the
floor sample order and the current B=4.3,A=3 residual budget. -/
theorem cover_of_sample_cycles (G : SimpleGraph V) (U : Finset V) (P : CyclePacking G)
    (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hxmax : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ 17/250)
    (hcard : U.card=⌊coverSampleP (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*(Fintype.card V:ℝ)⌋₊)
    (hcount : 2*P.count ≤ Fintype.card V-U.card)
    (hsingles : P.singles ≤ incidentEdgeCount G U+(Fintype.card V-U.card))
    (hincident : (incidentEdgeCount G U:ℝ) ≤ coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet)) :
    FineCover G 2 ∧ CoarseCover G 1 := by
  have hsize := twice_graph_edges_le_order_sq G
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  have hUn := card_le_univ U
  have hcountR : (P.count:ℝ) ≤ ((Fintype.card V:ℝ)-(U.card:ℝ))/2 := by
    have hh := (Nat.cast_le (α:=ℝ)).mpr hcount
    rw [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hUn] at hh
    linarith only [hh]
  have hbudget := cover_sample_count_within_cycle_budget (count:=(P.count:ℝ)) hn hm hsize hxmax
    (by rwa [hcard] at hcountR)
  have hsinglesR : (P.singles:ℝ) ≤ coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet)+(Fintype.card V:ℝ) := by
    have hh := (Nat.cast_le (α:=ℝ)).mpr hsingles
    rw [Nat.cast_add,Nat.cast_sub hUn] at hh
    linarith [Nat.cast_nonneg (α:=ℝ) U.card]
  have hhalf : (P.count:ℝ) ≤ (Fintype.card V:ℝ)/2 := by
    linarith [Nat.cast_nonneg (α:=ℝ) U.card]
  simp only [Set.fintypeCard_eq_ncard] at hbudget hsinglesR
  exact ⟨⟨P,hbudget,by linarith only [hsinglesR,hn]⟩,⟨P,hhalf,by simpa only [one_mul] using hsinglesR⟩⟩

end
end Cycle12
