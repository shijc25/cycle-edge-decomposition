import Cycle12.Foundations.AnchorWitnessProbability

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def AnchorSampleConditions (G : SimpleGraph V) (δ β lower upper : ℝ) (U : Finset V) : Prop :=
  lower ≤ (U.card:ℝ) ∧ (U.card:ℝ) ≤ upper ∧
    (∀ v, δ ≤ ((neighborsIn G v U).card:ℝ)) ∧ SampleCutExpansion G U β

def BadAnchorSample (G : SimpleGraph V) (δ β L lower upper : ℝ) (U : Finset V) : Prop :=
  AnchorSampleConditions G δ β lower upper U ∧ ∃ X C, BadAnchorCut G U X C L

def AnchorCopyWitness (G : SimpleGraph V) (δ β L lower upper err miss cap : ℝ)
    (U T : Finset V) (ξ : V→Option V) : Prop :=
  AnchorSampleConditions G δ β lower upper U ∧ ∃ X C, BadAnchorCut G U X C L ∧
    sampledErrorWeight G U C (U∩copiedSide T ξ (C∩T)) ≤ err*L*X.card ∧
      outsideCopyMisses X C T ξ ≤ miss*X.card ∧ (T.card:ℝ) ≤ cap

theorem bad_anchor_witness_transfer (G : SimpleGraph V) (p q : unitInterval)
    {δ β L lower upper err miss cap ω : ℝ}
    (hδ : 0 < δ) (hβ : 0 < β) (hL : 0 < L) (hLδ : L < δ)
    (herr : 0 < err) (hmiss : 0 < miss) (hmark : 1 ≤ (q:ℝ)*δ)
    (hcap : (q:ℝ)*upper ≤ cap) (hω : 0 ≤ ω)
    (hwitness : ω ≤ 1-(2+(δ/β)*exp (-(q:ℝ)*δ))/err-(L/δ+exp (-(q:ℝ)*δ))/miss-
      exp (-(cap-(q:ℝ)*upper)^2/(2*cap))) :
    ω*(bernoulliSubset p).prob (BadAnchorSample G δ β L lower upper) ≤
      (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
        (neighborCopyLaw G T).prob (AnchorCopyWitness G δ β L lower upper err miss cap U T))) := by
  let κ := fun U : Finset V => (subsetBernoulli U q).joint (neighborCopyLaw G)
  have hh := FiniteLaw.witness_transfer (bernoulliSubset p) κ
    (BadAnchorSample G δ β L lower upper)
    (fun U x => AnchorCopyWitness G δ β L lower upper err miss cap U x.1 x.2)
    hω (fun U hU => by
      obtain ⟨hcond,X,C,hbad⟩ := hU
      rw [FiniteLaw.prob_joint]
      apply hwitness.trans
      apply (anchor_copy_witness_probability G U X C q hδ hβ hL hLδ herr hmiss hmark
        hcond.2.2.1 hcond.2.2.2 hbad hcond.2.1 hcap).trans
      apply FiniteLaw.expect_mono
      intro T
      apply FiniteLaw.prob_mono
      intro ξ hξ
      exact ⟨hcond,X,C,hbad,hξ⟩)
  simpa only [κ,FiniteLaw.prob_joint] using hh

end
end Cycle13
