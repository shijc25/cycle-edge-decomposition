import Cycle12.CertifiedLocalFailure
import Cycle12.AcceptedGraphSampleTails
import Cycle12.FixedSampleSelection

namespace Cycle12
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cover_marked_state_z {g : RatMarkedGeometry} {G : SimpleGraph V}
    (st : CoverMarkedGraphState g G) :
    st.z=((st.N:ℝ)/(Fintype.card V:ℝ))*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet) := by
  rw [st.expansion_identity,← st.sample_fraction]
  exact (mul_div_cancel₀ _ st.fraction_pos.ne').symm

theorem cover_marked_states_same_sample {g h : RatMarkedGeometry} {G : SimpleGraph V}
    (s : CoverMarkedGraphState g G) (t : CoverMarkedGraphState h G) : s.N=t.N ∧ s.z=t.z := by
  have hn : s.N=t.N := s.sample_floor.trans t.sample_floor.symm
  refine ⟨hn,?_⟩
  rw [cover_marked_state_z s,cover_marked_state_z t,hn]

/-- The only probability premises are the three graph cut bounds. They
are instantiated by the independently checked anchor/global/local theorems. -/
theorem certified_sample_from_cut_bounds (moment : RatMomentEnvelope) (degree : RatDegreeEnvelope)
    (g : RatMarkedGeometry) (hmv : moment.Valid) (hdv : degree.NumericValid)
    (hmi : moment.inputs=g.inputs) (hdi : degree.inputs=g.inputs)
    (G : SimpleGraph V) (st : CoverMarkedGraphState g G)
    (hs : (g.inputs.s0:ℝ) ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet))
    (hdegree : ∀ v, coverDeleteThreshold (Fintype.card V) (Fintype.card G.edgeSet) ≤ (G.degree v:ℝ))
    {beta L bCut bAnchor bExtra : ℝ} (extraBad : Finset V → Prop)
    (hCut : (fixedSizeLaw (univ:Finset V) st.N).prob
      (FixedExpansionFailure G univ st.N st.z degree.dm beta) ≤ bCut)
    (hAnchor : (fixedSizeLaw (univ:Finset V) st.N).prob
      (FixedAnchorFailure G st.N st.z degree.dm beta L) ≤ bAnchor)
    (hExtra : (fixedSizeLaw (univ:Finset V) st.N).prob extraBad ≤ bExtra)
    (hsum : (degree.probability:ℝ)+bCut+bAnchor+(moment.edgeProbability:ℝ)+
      (moment.incidentProbability:ℝ)+bExtra < 1) :
    ∃ U : Finset V, U.card=st.N ∧
      GoodVertexSample G U ((degree.dm:ℝ)*st.z) (beta*st.z) L st.N st.N
        ((97/100)*((st.N:ℝ)/(Fintype.card V:ℝ))^2*(Fintype.card G.edgeSet:ℝ))
        (coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet)) ∧ ¬extraBad U := by
  have htails := rat_moment_actual_graph_tails moment hmv G st.mass_pos
    (by rw [hmi]; exact st.x_lower) (by rw [hmi]; exact st.x_upper)
    (by rw [hmi]; exact hs) st.sample_floor
  have hi : degree.inputs.Valid := by rw [hdi,← hmi]; exact hmv.1
  have hdeg := rat_degree_actual_graph_tail degree hi hdv G st.mass_pos
    (by rw [hdi]; exact st.x_lower) (by rw [hdi]; exact st.x_upper)
    (by rw [hdi]; exact hs) st.sample_floor hdegree
  rw [← cover_marked_state_z st] at hdeg
  apply exists_fixed_sample_of_failure_bounds G st.sample_le_order extraBad
    (bDegree:=(degree.probability:ℝ)) (bCut:=bCut) (bAnchor:=bAnchor)
    (bEdge:=(moment.edgeProbability:ℝ)) (bIncident:=(moment.incidentProbability:ℝ)) (bExtra:=bExtra)
    ?_ hCut hAnchor ?_ ?_ hExtra hsum
  · exact (FiniteLaw.prob_mono _ (by rintro U ⟨v,hv⟩; exact ⟨v,hv.le⟩)).trans hdeg
  · exact (FiniteLaw.prob_mono _ (fun U h => h.le)).trans htails.1
  · exact (FiniteLaw.prob_mono _ (fun U h => h.le)).trans htails.2

theorem good_sample_local_of_no_failure (G : SimpleGraph V) (U : Finset V)
    {N : ℕ} {z dm beta L edgeLower incidentUpper localBeta : ℝ}
    (hcard : U.card=N)
    (hgood : GoodVertexSample G U (dm*z) (beta*z) L N N edgeLower incidentUpper)
    (hno : ¬FixedRestrictedCutFailure G univ N z dm localBeta (1/125) U) :
    LocalSampleCutExpansion G U (localBeta*z) (1/125) := by
  apply fixed_local_expansion_of_not_failure G U hcard _ hno
  exact fun v _ => hgood.neighbors v

end
end Cycle12
