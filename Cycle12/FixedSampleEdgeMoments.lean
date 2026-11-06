import Cycle12.FixedContainmentExact
import Cycle12.EdgePairClassification
import Cycle12.Foundations.FiniteSecondMoment

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def fixedChooseRatio (n k j : ℕ) : ℝ := (k.choose j:ℝ)/(n.choose j:ℝ)

theorem fixed_sample_edge_mean (G : SimpleGraph V) {k : ℕ} (hk : k≤Fintype.card V) :
    (fixedSizeLaw (univ:Finset V) k).expect (fun S => (sampledFinsetEdgeCount G S:ℝ))=
      (Fintype.card G.edgeSet:ℝ)*fixedChooseRatio (Fintype.card V) k 2 := by
  simp_rw [sampled_finset_edge_count,occurrenceCount,FiniteLaw.expect_sum]
  have hi (e : G.edgeSet) := fixed_size_indicator_expect univ (edgeVertexSet G e)
    (subset_univ _) (by simpa using hk)
  simp only [edgeVertexSet_card,card_univ] at hi
  simp_rw [hi]
  simp only [sum_const,card_univ,nsmul_eq_mul,fixedChooseRatio]

theorem fixed_sample_edge_pair_moment (G : SimpleGraph V) {k : ℕ}
    (hk : k≤Fintype.card V) (e f : G.edgeSet) :
    (fixedSizeLaw (univ:Finset V) k).expect
        (fun S => containsIndicator (edgeVertexSet G e) S*containsIndicator (edgeVertexSet G f) S)=
      if e=f then fixedChooseRatio (Fintype.card V) k 2
      else if G.lineGraph.Adj e f then fixedChooseRatio (Fintype.card V) k 3
      else fixedChooseRatio (Fintype.card V) k 4 := by
  rw [fixed_size_indicator_product univ _ _ (subset_univ _) (subset_univ _) (by simpa using hk)]
  by_cases hef : e=f
  · subst f
    simp only [if_true,union_self,edgeVertexSet_card,card_univ,fixedChooseRatio]
  · rw [if_neg hef]
    by_cases ha : G.lineGraph.Adj e f
    · rw [if_pos ha,edge_vertex_union_card_adjacent G e f ha,card_univ]
      rfl
    · rw [if_neg ha,edge_vertex_union_card_disjoint G e f hef ha,card_univ]
      rfl

theorem fixed_sample_edge_second_moment (G : SimpleGraph V) {k : ℕ}
    (hk : k≤Fintype.card V) :
    (fixedSizeLaw (univ:Finset V) k).expect (fun S => (sampledFinsetEdgeCount G S:ℝ)^2)=
      (Fintype.card G.edgeSet:ℝ)*fixedChooseRatio (Fintype.card V) k 2+
      ((∑ v, (G.degree v:ℝ)^2)-2*(Fintype.card G.edgeSet:ℝ))*fixedChooseRatio (Fintype.card V) k 3+
      ((Fintype.card G.edgeSet:ℝ)^2+(Fintype.card G.edgeSet:ℝ)-(∑ v, (G.degree v:ℝ)^2))*
        fixedChooseRatio (Fintype.card V) k 4 := by
  simp_rw [sampled_finset_edge_count,occurrenceCount]
  rw [FiniteLaw.expect_sum_sq]
  simp_rw [fixed_sample_edge_pair_moment G hk]
  exact ordered_edge_pair_function_sum G _ _ _

/-- The exact variance identity for the edge count in an actual uniform
k-vertex sample. This is valid even for small k, with binomial ratios. -/
theorem fixed_sample_edge_variance_identity (G : SimpleGraph V) {k : ℕ}
    (hk : k≤Fintype.card V) :
    (fixedSizeLaw (univ:Finset V) k).expect
      (fun S => ((sampledFinsetEdgeCount G S:ℝ)-
        (Fintype.card G.edgeSet:ℝ)*fixedChooseRatio (Fintype.card V) k 2)^2)=
      (Fintype.card G.edgeSet:ℝ)*(fixedChooseRatio (Fintype.card V) k 2-
        2*fixedChooseRatio (Fintype.card V) k 3+fixedChooseRatio (Fintype.card V) k 4)+
      (∑ v, (G.degree v:ℝ)^2)*(fixedChooseRatio (Fintype.card V) k 3-
        fixedChooseRatio (Fintype.card V) k 4)+
      (Fintype.card G.edgeSet:ℝ)^2*(fixedChooseRatio (Fintype.card V) k 4-
        (fixedChooseRatio (Fintype.card V) k 2)^2) := by
  rw [FiniteLaw.centered_second_moment _ _ (fixed_sample_edge_mean G hk),
    fixed_sample_edge_second_moment G hk]
  ring

end
end Cycle12
