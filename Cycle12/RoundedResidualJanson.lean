import Cycle12.TruncatedResidualGraph
import Cycle12.FixedGraphMassJanson
import Cycle12.Foundations.RoundedTruncation

namespace Cycle12
open Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem rounded_cut_cap_ge_card (S : Finset V) {lambda : ℝ} (hl : 1 ≤ lambda) :
    S.card ≤ roundedCutCap lambda S := by
  have hs : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  have hh : (S.card:ℝ) ≤ lambda*S.card := by nlinarith
  exact_mod_cast hh.trans (roundedCutCap_lower lambda S)

theorem rounded_residual_endpoint_budget (G : SimpleGraph V) (S T : Finset V)
    {lambda : ℝ} (hl : 1 ≤ lambda) :
    (∑ e : (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet,
      ((truncatedResidualGraph G S T (roundedCutCap lambda S)).lineGraph.degree e:ℝ))  ≤ 
      ((lambda+1)*S.card)*(Fintype.card
        (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ) := by
  have hh := truncated_subgraph_line_bound G _ S (roundedCutCap lambda S)
    (truncated_residual_le G S T _)
  have hu := roundedCutCap_upper (show 0 ≤ lambda by linarith) S
  have hd : (roundedCutCap lambda S:ℝ)+S.card-2 ≤ (lambda+1)*S.card := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α:=ℝ)
    (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet))
  exact hh.trans (by simpa only [mul_comm] using hm)

theorem rounded_residual_rectangle_budget (G : SimpleGraph V) (S T : Finset V)
    (hS : S.Nonempty) {lambda : ℝ} (hl : 1 ≤ lambda) :
    (∑ e : (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet,
      ((truncatedResidualGraph G S T (roundedCutCap lambda S)).lineGraph.degree e:ℝ))  ≤ 
      (lambda*S.card+1)*(Fintype.card
        (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ)+
      (1/(lambda*S.card))*(Fintype.card
        (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ)^2 := by
  let H := truncatedResidualGraph G S T (roundedCutCap lambda S)
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hc : S.card ≤ roundedCutCap lambda S := rounded_cut_cap_ge_card S hl
  have hk : 0<roundedCutCap lambda S := hS.card_pos.trans_le hc
  have hrect := truncated_subgraph_rectangle G H S (roundedCutCap lambda S)
    (truncated_residual_le G S T _) hk hc
  have hline := (graph_line_degree_square_bound H).trans hrect
  have hfirst := mul_le_mul_of_nonneg_right
    (roundedCutCap_upper (show 0 ≤ lambda by linarith) S)
    (Nat.cast_nonneg (α:=ℝ) (Fintype.card H.edgeSet))
  have hsecond := div_le_div_of_nonneg_left (sq_nonneg (Fintype.card H.edgeSet:ℝ))
    (mul_pos (show 0<lambda by linarith) hs) (roundedCutCap_lower lambda S)
  apply hline.trans
  have hh := add_le_add hfirst hsecond
  simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh

/-- A fixed-size tail for the actual capped cut after deleting the marks.
The better of the two dependency bounds is selected after substituting
the certified edge lower bound into a proved monotone exponent. -/
theorem rounded_residual_sharp_janson (G : SimpleGraph V) (S T : Finset V)
    (hS : S.Nonempty) {lambda : ℝ} (hl : 1 ≤ lambda) (p : unitInterval)
    {k : ℕ} (hk : k ≤ (univ\T).card)
    (hmean : ((univ\T).card:ℝ)*(p:ℝ)=(k:ℝ))
    (hp : (p:ℝ) ≤ 1/2) (hp0 : 0<(p:ℝ))
    {M : ℝ} (hM : 0<M)
    (hret : M ≤ (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ))
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (fixedSizeLaw (univ\T) k).prob (fun R =>
      (sampledFinsetEdgeCount (truncatedResidualGraph G S T (roundedCutCap lambda S)) R:ℝ)  ≤ 
        tau*(M*(p:ℝ)^2))  ≤ 
      2*Real.exp (-fullJansonPhi tau*M*(p:ℝ)^2/
        (1+min ((lambda+1)*S.card) (lambda*S.card+1+M/(lambda*S.card))*(p:ℝ))) := by
  let H := truncatedResidualGraph G S T (roundedCutCap lambda S)
  have hD : ∀ e : H.edgeSet, edgeVertexSet H e⊆univ\T :=
    retained_vertex_graph_edge_support _ _
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hla : 0 ≤ lambda := by linarith
  have h₁ := fixed_graph_quadratic_janson H (univ\T) hD p hk hmean hp hp0 hM hret
    (a:=(lambda+1)*S.card) (b:=0) (by positivity) (by norm_num)
    (by simpa only [zero_mul,add_zero] using rounded_residual_endpoint_budget G S T hl)
    tau ht0 ht1
  have h₂ := fixed_graph_quadratic_janson H (univ\T) hD p hk hmean hp hp0 hM hret
    (a:=lambda*S.card+1) (b:=1/(lambda*S.card)) (by positivity) (by positivity)
    (rounded_residual_rectangle_budget G S T hS hl) tau ht0 ht1
  simp only [zero_mul,add_zero] at h₁
  have he : (1/(lambda*S.card))*M=M/(lambda*S.card) := by ring
  rw [he] at h₂
  by_cases hd : (lambda+1)*S.card ≤ lambda*S.card+1+M/(lambda*S.card)
  · rw [min_eq_left hd]
    exact h₁
  · rw [min_eq_right (le_of_not_ge hd)]
    exact h₂

end
end Cycle12
