import Cycle12.CertifiedSampleSelection

namespace Cycle12
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

structure RatSamplerCase where
  moment : RatMomentEnvelope
  degree : RatDegreeEnvelope
  beta : ℚ
  L : ℚ
  localBeta : Option ℚ
  cutBound : ℚ
  anchorBound : ℚ
  extraBound : ℚ

def RatSamplerCase.NumericValid (c : RatSamplerCase) : Prop :=
  c.degree.probability+c.cutBound+c.anchorBound+c.moment.edgeProbability+c.moment.incidentProbability+c.extraBound < 1

instance instDecidableRatSamplerCaseNumeric (c : RatSamplerCase) : Decidable c.NumericValid := by
  unfold RatSamplerCase.NumericValid
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

def RatSamplerCase.extraBad (c : RatSamplerCase) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N : ℕ) (z : ℝ) (U : Finset V) : Prop :=
  match c.localBeta with
  | none => False
  | some b => FixedRestrictedCutFailure G univ N z c.degree.dm b (1/125) U

def RatSamplerCase.Good (c : RatSamplerCase) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N : ℕ) (z : ℝ) : Prop :=
  ∃ U : Finset V, U.card=N ∧
    GoodVertexSample G U ((c.degree.dm:ℝ)*z) ((c.beta:ℝ)*z) c.L N N
      ((97/100)*((N:ℝ)/(Fintype.card V:ℝ))^2*(Fintype.card G.edgeSet:ℝ))
      (coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet)) ∧
    (match c.localBeta with | none => True | some b => LocalSampleCutExpansion G U ((b:ℝ)*z) (1/125))

def RatSamplerCase.Sound (c : RatSamplerCase) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (0:ℝ) < Fintype.card G.edgeSet →
    (c.moment.inputs.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) →
    coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (c.moment.inputs.xh:ℝ) →
    (c.moment.inputs.s0:ℝ) ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet) →
    (∀ v, coverDeleteThreshold (Fintype.card V) (Fintype.card G.edgeSet) ≤ (G.degree v:ℝ)) →
    CoverSparseCutIrreducible G →
    let N := ⌊coverSampleP (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*(Fintype.card V:ℝ)⌋₊
    let z := ((N:ℝ)/(Fintype.card V:ℝ))*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)
    c.Good G N z

theorem rat_sampler_case_good_from_cut_bounds (c : RatSamplerCase) (g : RatMarkedGeometry)
    (hc : c.NumericValid) (hmv : c.moment.Valid) (hdv : c.degree.NumericValid)
    (hmi : c.moment.inputs=g.inputs) (hdi : c.degree.inputs=g.inputs)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (st : CoverMarkedGraphState g G)
    (hs : (g.inputs.s0:ℝ) ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet))
    (hdegree : ∀ v, coverDeleteThreshold (Fintype.card V) (Fintype.card G.edgeSet) ≤ (G.degree v:ℝ))
    (hCut : (fixedSizeLaw (univ:Finset V) st.N).prob
      (FixedExpansionFailure G univ st.N st.z c.degree.dm c.beta) ≤ (c.cutBound:ℝ))
    (hAnchor : (fixedSizeLaw (univ:Finset V) st.N).prob
      (FixedAnchorFailure G st.N st.z c.degree.dm c.beta c.L) ≤ (c.anchorBound:ℝ))
    (hExtra : (fixedSizeLaw (univ:Finset V) st.N).prob (c.extraBad G st.N st.z) ≤ (c.extraBound:ℝ)) :
    c.Good G st.N st.z := by
  have hsum : (c.degree.probability:ℝ)+(c.cutBound:ℝ)+(c.anchorBound:ℝ)+(c.moment.edgeProbability:ℝ)+
      (c.moment.incidentProbability:ℝ)+(c.extraBound:ℝ) < 1 := by exact_mod_cast hc
  obtain ⟨U,hcard,hgood,hno⟩ := certified_sample_from_cut_bounds c.moment c.degree g hmv hdv hmi hdi G st hs
    hdegree (c.extraBad G st.N st.z) hCut hAnchor hExtra hsum
  refine ⟨U,hcard,hgood,?_⟩
  cases he : c.localBeta with
  | none => simp only [he]
  | some b =>
    simp only [he]
    apply good_sample_local_of_no_failure G U hcard hgood
    simpa only [RatSamplerCase.extraBad,he] using hno

end
end Cycle12
