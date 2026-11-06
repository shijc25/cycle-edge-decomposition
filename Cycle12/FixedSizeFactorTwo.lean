import Cycle12.BinomialMeanMedianHalf
import Cycle12.BipartiteRectangle

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Factor-two transfer with its binomial median premise fully discharged
in the sampling range p≤1/2. -/
theorem fixed_size_decreasing_factor_two (D : Finset V) (p : unitInterval)
    {k : ℕ} (hk : k≤D.card) (hmean : (D.card:ℝ)*(p:ℝ)=(k:ℝ))
    (hp : (p:ℝ)≤1/2) (E : Finset V → Prop)
    (hE : ∀ S T, S⊆T → E T → E S) :
    (fixedSizeLaw D k).prob E ≤ 2*(subsetBernoulli D p).prob E := by
  have hw := bernoulli_to_fixed_decreasing_weighted D p hk E hE
  have hm : (1:ℝ)/2≤(subsetBernoulli D p).prob (fun S => S.card≤k) := by
    rw [bernoulli_card_cdf_polynomial D p hk]
    exact binomial_integer_mean_lower_half D.card k p p.2.1 hp hmean
  have hn := (fixedSizeLaw D k).prob_nonneg E
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) hn]

theorem sampled_finset_edge_count_monotone (G : SimpleGraph V) :
    Monotone (fun S => (sampledFinsetEdgeCount G S:ℝ)) := by
  intro S T hST
  change (sampledFinsetEdgeCount G S:ℝ)≤(sampledFinsetEdgeCount G T:ℝ)
  rw [sampled_finset_edge_count,sampled_finset_edge_count]
  exact sum_le_sum (fun e _ => contains_indicator_monotone (edgeVertexSet G e) hST)

theorem fixed_sample_sharp_janson (G : SimpleGraph V) (p : unitInterval)
    {k : ℕ} (hk : k≤Fintype.card V) (hmean : (Fintype.card V:ℝ)*(p:ℝ)=(k:ℝ))
    (hp : (p:ℝ)≤1/2) (hm : 0<(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)
    (Q : ℝ) (hQ : (∑ v, (G.degree v:ℝ)^2)≤Q)
    (tau : ℝ) (ht0 : 0≤tau) (ht1 : tau≤1) :
    (fixedSizeLaw (univ:Finset V) k).prob
        (fun S => (sampledFinsetEdgeCount G S:ℝ)≤tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)) ≤
      2*Real.exp (-fullJansonPhi tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2/
        ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+Q*(p:ℝ)^3)) := by
  apply (fixed_size_decreasing_factor_two (univ:Finset V) p (by simpa using hk)
    (by simpa using hmean) hp _ (fun S T hST hT =>
      (sampled_finset_edge_count_monotone G hST).trans hT)).trans
  exact mul_le_mul_of_nonneg_left (graph_janson_square_lower_tail G p hm Q hQ tau ht0 ht1)
    (by norm_num)

end
end Cycle12
