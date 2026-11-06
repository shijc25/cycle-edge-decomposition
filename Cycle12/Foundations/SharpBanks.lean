import Cycle12.Foundations.SharpAllCuts
import Cycle12.Foundations.StrongBank
import Cycle12.Foundations.WeakBank
import Cycle12.Foundations.SampledCyclePacking
import Cycle12.Foundations.SampleGraphBounds

namespace Cycle13
open SimpleGraph Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable

theorem exists_weak_routing_bank {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : unitInterval) {E N D T d g f ε a b c : ℝ}
    (hT : 5 ≤ T) (hTD : 7*T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V:ℝ) ≤ N)
    (hE : E ≤ (1-(q:ℝ)-ε)*G.edgeSet.ncard) (hdense : D*N-D^2/2 ≤ E)
    (hbase : ∀ v, d ≤ (G.degree v:ℝ))
    (hg0 : 0 ≤ g) (hgq : g < (q:ℝ)) (hε : 0 ≤ ε)
    (hcut : (edgeSplitMeasure V q).real {ω |
      ¬∀ S : Finset V, f*cutSize G S ≤ (cutSize (splitBank G ω true) S:ℝ)} ≤ a)
    (hcore : exp (-2*ε^2*G.edgeSet.ncard) ≤ b)
    (hbranch : (g=f ∧ 0 ≤ c) ∨ Fintype.card V*exp (-2*D*((q:ℝ)-g)^2/(1-g)) ≤ c)
    (hbudget : a+b+c < 1) :
    ∃ J : WeakCliqueImmersion (evenFloor (T-1)) G,
      (∀ S : Finset V, f*cutSize G S ≤ (cutSize J.residue S:ℝ)) ∧
      ∀ i, max (D/(1-g)) d-11/10*T ≤ (J.residue.degree (J.branch i):ℝ) := by
  obtain ⟨ω,hωcut,hωcore,hωbranch⟩ := exists_simultaneous_edge_split G q (by linarith : 0 < D)
    hg0 hgq hε hcut hcore hbranch hbudget
  have hpart := splitBank_partition G ω
  have hEcore : E ≤ ((splitBank G ω false).edgeFinset.card:ℝ) := by
    have hh := hE.trans hωcore
    simpa only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using hh
  obtain ⟨J,hF,hdegree⟩ := exists_dense_recycled_weak_model G (splitBank G ω true)
    (splitBank G ω false) hpart.1 hpart.2 hT hTD hDN horder hEcore hdense
    (hgq.trans_le q.2.2) hωbranch hbase
  refine ⟨J,?_,hdegree⟩
  intro S
  exact (hωcut S).trans (by exact_mod_cast cutSize_mono hF S)

theorem exists_strong_sample_bank {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (q : unitInterval)
    {δ β L lower upper edgeLower incidentUpper E N D T g f ε a b c : ℝ}
    (hU : GoodVertexSample G U δ β L lower upper edgeLower incidentUpper)
    (hβ : 1 ≤ β) (hδ : 0 < δ) (hn : 2 ≤ U.card)
    (hT : 4 ≤ T) (hTD : T ≤ D) (hDN : D ≤ N)
    (horder : (U.card:ℝ) ≤ N)
    (hE : E ≤ (1-(q:ℝ)-ε)*(sampledEdgeCount G (U:Set V):ℝ))
    (hdense : D*N-D^2/2 ≤ E) (hstop : T*(1+log (N/T)) ≤ 2*E/N)
    (hg0 : 0 ≤ g) (hgq : g < (q:ℝ)) (hε : 0 ≤ ε) (hfq : f ≤ (q:ℝ))
    (hgap : 0 < 2*((q:ℝ)-f)^2*δ-2*log (U.card:ℝ))
    (hcut : sharpCutFailure U.card ((q:ℝ)-f) δ ≤ a)
    (hcore : exp (-2*ε^2*(sampledEdgeCount G (U:Set V):ℝ)) ≤ b)
    (hbranch : (g=f ∧ 0 ≤ c) ∨ (U.card:ℝ)*exp (-2*D*((q:ℝ)-g)^2/(1-g)) ≤ c)
    (hbudget : a+b+c < 1) :
    Nonempty (SampleRoutingBank G U (evenFloor T) f (max (D/(1-g)) δ-T)) := by
  let H := G.induce (U:Set V)
  have hfail := (edge_split_all_cuts_failure_sharp H q (sub_nonneg.mpr hfq) hδ
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hn) (hU.induced_mincut G U hβ)
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hgap)).trans (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hcut)
  simp only [sub_sub_cancel] at hfail
  have hbase : ∀ v : U, δ ≤ (H.degree v:ℝ) := by
    intro v
    have he := sample_induced_degree G U v
    have hh := hU.neighbors v.val
    rw [← he] at hh
    simpa only [H,SimpleGraph.degree,SimpleGraph.neighborFinset,Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using hh
  obtain ⟨J,_,_,hcuts,hdegree⟩ := exists_strong_routing_bank H q hT hTD hDN
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using horder)
    (by simpa only [H,sample_induced_edge_count] using hE) hdense hstop hbase hg0 hgq hε hfail
    (by simpa only [H,sample_induced_edge_count] using hcore)
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hbranch) hbudget
  exact ⟨⟨J.toWeak,hcuts,hdegree⟩⟩

theorem exists_weak_sample_bank {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (q : unitInterval)
    {δ β L lower upper edgeLower incidentUpper E N D T g f ε a b c : ℝ}
    (hU : GoodVertexSample G U δ β L lower upper edgeLower incidentUpper)
    (hβ : 1 ≤ β) (hδ : 0 < δ) (hn : 2 ≤ U.card)
    (hT : 5 ≤ T) (hTD : 7*T ≤ D) (hDN : D ≤ N)
    (horder : (U.card:ℝ) ≤ N)
    (hE : E ≤ (1-(q:ℝ)-ε)*(sampledEdgeCount G (U:Set V):ℝ))
    (hdense : D*N-D^2/2 ≤ E)
    (hg0 : 0 ≤ g) (hgq : g < (q:ℝ)) (hε : 0 ≤ ε) (hfq : f ≤ (q:ℝ))
    (hgap : 0 < 2*((q:ℝ)-f)^2*δ-2*log (U.card:ℝ))
    (hcut : sharpCutFailure U.card ((q:ℝ)-f) δ ≤ a)
    (hcore : exp (-2*ε^2*(sampledEdgeCount G (U:Set V):ℝ)) ≤ b)
    (hbranch : (g=f ∧ 0 ≤ c) ∨ (U.card:ℝ)*exp (-2*D*((q:ℝ)-g)^2/(1-g)) ≤ c)
    (hbudget : a+b+c < 1) :
    Nonempty (SampleRoutingBank G U (evenFloor (T-1)) f (max (D/(1-g)) δ-11/10*T)) := by
  let H := G.induce (U:Set V)
  have hfail := (edge_split_all_cuts_failure_sharp H q (sub_nonneg.mpr hfq) hδ
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hn) (hU.induced_mincut G U hβ)
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hgap)).trans (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hcut)
  simp only [sub_sub_cancel] at hfail
  have hbase : ∀ v : U, δ ≤ (H.degree v:ℝ) := by
    intro v
    have he := sample_induced_degree G U v
    have hh := hU.neighbors v.val
    rw [← he] at hh
    simpa only [H,SimpleGraph.degree,SimpleGraph.neighborFinset,Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using hh
  obtain ⟨J,hcuts,hdegree⟩ := exists_weak_routing_bank H q hT hTD hDN
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using horder)
    (by simpa only [H,sample_induced_edge_count] using hE) hdense hbase hg0 hgq hε hfail
    (by simpa only [H,sample_induced_edge_count] using hcore)
    (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hbranch) hbudget
  exact ⟨⟨J,hcuts,hdegree⟩⟩

end
end Cycle13
