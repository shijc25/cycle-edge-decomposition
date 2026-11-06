import Cycle12.Foundations.BernoulliContainment
import Cycle12.Foundations.FiniteSecondMoment
import Cycle12.Foundations.GraphJanson

/-! The actual vertex-sampled graph edge count and its variance. Adjacent
edge pairs are counted with order, retaining the factor (1-p). -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem sampledEdgeCount_eq_sum (G : SimpleGraph V) (S : Finset V) :
    (sampledEdgeCount G (S:Set V):ℝ)=∑ e : G.edgeSet, containsIndicator (edgeVertexSet G e) S := by
  simp only [containsIndicator]
  rw [Finset.sum_boole]
  congr 1
  simp only [sampledEdgeCount,Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp

theorem sampledEdgeCount_expect (G : SimpleGraph V) (p : unitInterval) :
    (bernoulliSubset (V:=V) p).expect (fun S => (sampledEdgeCount G (S:Set V):ℝ))=
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2 := by
  simp_rw [sampledEdgeCount_eq_sum,FiniteLaw.expect_sum,bernoulliSubset_contains_expect,
    edgeVertexSet_card]
  simp

theorem edge_indicator_covariance_bound (G : SimpleGraph V) (p : unitInterval)
    (e f : G.edgeSet) :
    (bernoulliSubset (V:=V) p).expect (fun S =>
      containsIndicator (edgeVertexSet G e) S*containsIndicator (edgeVertexSet G f) S)-
        (p:ℝ)^2*(p:ℝ)^2 ≤
      (if e=f then (p:ℝ)^2 else 0)+
        (if G.lineGraph.Adj e f then (p:ℝ)^3*(1-(p:ℝ)) else 0) := by
  rw [bernoulliSubset_contains_product]
  by_cases hef : e=f
  · subst f
    simp only [union_self,edgeVertexSet_card,ite_true,SimpleGraph.irrefl,ite_false,add_zero]
    nlinarith [sq_nonneg ((p:ℝ)^2)]
  · rw [if_neg hef]
    by_cases hadj : G.lineGraph.Adj e f
    · rw [if_pos hadj,zero_add]
      have hh := pow_le_pow_of_le_one p.2.1 p.2.2 (edgeVertexSet_union_card G e f hef)
      nlinarith
    · rw [if_neg hadj,zero_add]
      have hd : Disjoint (edgeVertexSet G e) (edgeVertexSet G f) := by
        apply Finset.disjoint_coe.mp
        apply edgeDependencies_valid G e f hef
        simpa only [edgeDependencies,mem_filter,mem_univ,true_and] using hadj
      rw [card_union_of_disjoint hd,edgeVertexSet_card,edgeVertexSet_card]
      norm_num only
      nlinarith

theorem sampledEdgeCount_variance_dependencies (G : SimpleGraph V) (p : unitInterval) :
    (bernoulliSubset (V:=V) p).expect (fun S =>
      ((sampledEdgeCount G (S:Set V):ℝ)-(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2) ≤
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
        ((edgeDependencies G).card:ℝ)*(p:ℝ)^3*(1-(p:ℝ)) := by
  have hm : ∀ e : G.edgeSet, (bernoulliSubset p).expect
      (containsIndicator (edgeVertexSet G e))=(p:ℝ)^2 := by
    intro e; rw [bernoulliSubset_contains_expect,edgeVertexSet_card]
  have hh := FiniteLaw.variance_sum (bernoulliSubset p)
    (fun e : G.edgeSet => containsIndicator (edgeVertexSet G e)) (fun _ => (p:ℝ)^2) hm
  simp only [sum_const,card_univ,nsmul_eq_mul] at hh
  simp_rw [← sampledEdgeCount_eq_sum G] at hh
  rw [hh]
  apply le_trans (sum_le_sum (s:=univ) (fun e _ =>
    sum_le_sum (s:=univ) (fun f _ => edge_indicator_covariance_bound G p e f)))
  simp_rw [sum_add_distrib]
  have hdiag : (∑ e : G.edgeSet, ∑ f : G.edgeSet, if e=f then (p:ℝ)^2 else 0)=
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2 := by simp
  rw [hdiag]
  have hadj : (∑ e : G.edgeSet, ∑ f : G.edgeSet,
      if G.lineGraph.Adj e f then (p:ℝ)^3*(1-(p:ℝ)) else 0)=
      ((edgeDependencies G).card:ℝ)*((p:ℝ)^3*(1-(p:ℝ))) := by
    rw [← Fintype.sum_prod_type (fun q : G.edgeSet×G.edgeSet =>
      if G.lineGraph.Adj q.1 q.2 then (p:ℝ)^3*(1-(p:ℝ)) else 0),← sum_filter]
    simp only [edgeDependencies,sum_const,nsmul_eq_mul]
  rw [hadj]
  ring_nf
  exact le_rfl

theorem sampledEdgeCount_variance (G : SimpleGraph V) (p : unitInterval) {r : ℕ}
    (hdeg : ∀ v, G.degree v ≤ r) :
    (bernoulliSubset (V:=V) p).expect (fun S =>
      ((sampledEdgeCount G (S:Set V):ℝ)-(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2) ≤
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
        2*(Fintype.card G.edgeSet:ℝ)*r*(p:ℝ)^3*(1-(p:ℝ)) := by
  have hc : (edgeDependencies G).card ≤ Fintype.card G.edgeSet*(2*r) := by
    rw [edgeDependencies_card]
    calc
      _ ≤ ∑ _e : G.edgeSet, 2*r := by
        apply sum_le_sum; intro e _
        have he := lineGraph_degree_bound G e
        have h₁ := hdeg e.val.out.1
        have h₂ := hdeg e.val.out.2
        omega
      _ = _ := by simp
  have hcR : ((edgeDependencies G).card:ℝ) ≤ (Fintype.card G.edgeSet:ℝ)*(2*r) := by
    exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_right hcR
    (mul_nonneg (pow_nonneg p.2.1 3) (sub_nonneg.mpr p.2.2))
  have hv := sampledEdgeCount_variance_dependencies G p
  nlinarith

theorem sampledEdgeCount_cantelli (G : SimpleGraph V) (p : unitInterval) {r : ℕ}
    (hdeg : ∀ v, G.degree v ≤ r) {t : ℝ} (ht : 0<t) :
    (bernoulliSubset (V:=V) p).prob (fun S =>
      (sampledEdgeCount G (S:Set V):ℝ) ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2-t) ≤
    ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+2*(Fintype.card G.edgeSet:ℝ)*r*(p:ℝ)^3*(1-(p:ℝ)))/
      ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+2*(Fintype.card G.edgeSet:ℝ)*r*(p:ℝ)^3*(1-(p:ℝ))+t^2) :=
  FiniteLaw.cantelli_lower _ _ (sampledEdgeCount_expect G p) (sampledEdgeCount_variance G p hdeg) ht

end
end Cycle13
