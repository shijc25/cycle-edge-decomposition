import Cycle12.Foundations.BadCutWitnessTransfer

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem neighborCopy_fixed_uniform_witness (G : SimpleGraph V) (U A : Finset V)
    (q : unitInterval) {δ β err upper cap : ℝ}
    (hδ : 0 < δ) (hmark : 1 ≤ (q:ℝ)*δ) (herr : 0 < err)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hupper : (U.card:ℝ) ≤ upper) (hcap : (q:ℝ)*upper ≤ cap)
    (hA : BadSampleCut G U A β) :
    1-(2*β+δ*exp (-(q:ℝ)*δ))/err-exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) ≤
    (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).prob (fun ξ =>
      sampledErrorWeight G U A (U∩copiedSide T ξ (A∩T)) ≤ err*A.card ∧ (T.card:ℝ) ≤ cap)) := by
  have hq : 0 < (q:ℝ) := by nlinarith [q.2.1]
  have hU : 0 < (U.card:ℝ) := hA.2.1.trans_le (by exact_mod_cast card_le_card hA.1)
  have hμ : 0 < (q:ℝ)*U.card := mul_pos hq hU
  have hμmax := mul_le_mul_of_nonneg_left hupper q.2.1
  have hcapU : (q:ℝ)*U.card ≤ cap := hμmax.trans hcap
  have hcap0 : 0 < cap := hμ.trans_le hcapU
  have hh := neighborCopy_cut_witness G U A hA.1 hA.2.1 q hδ hmark hdeg herr hA.2.2.2 hμ hcapU
  have htail : exp (-(cap-(q:ℝ)*U.card)^2/(2*cap)) ≤
      exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) := by
    apply exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num : (0:ℝ) < 2) hcap0)).mpr
    nlinarith
  linarith

def BadCutWithin (G : SimpleGraph V) (δ β upper : ℝ)
    (allowed : Finset V→Finset V→Prop) (U : Finset V) : Prop :=
  (U.card:ℝ) ≤ upper ∧ (∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ)) ∧
    ∃ A, BadSampleCut G U A β ∧ allowed U A

def CutWitnessWithin (G : SimpleGraph V) (δ β err upper cap : ℝ)
    (allowed : Finset V→Finset V→Prop) (U T : Finset V) (ξ : V→Option V) : Prop :=
  (U.card:ℝ) ≤ upper ∧ (∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ)) ∧
    ∃ A, BadSampleCut G U A β ∧ allowed U A ∧
      sampledErrorWeight G U A (U∩copiedSide T ξ (A∩T)) ≤ err*A.card ∧ (T.card:ℝ) ≤ cap

theorem bad_cut_within_witness_transfer (G : SimpleGraph V) (p q : unitInterval)
    (allowed : Finset V→Finset V→Prop)
    {δ β err upper cap ω : ℝ} (hδ : 0 < δ) (hmark : 1 ≤ (q:ℝ)*δ)
    (herr : 0 < err) (hcap : (q:ℝ)*upper ≤ cap) (hω0 : 0 ≤ ω)
    (hω : ω ≤ 1-(2*β+δ*exp (-(q:ℝ)*δ))/err-exp (-(cap-(q:ℝ)*upper)^2/(2*cap))) :
    ω*(bernoulliSubset p).prob (BadCutWithin G δ β upper allowed) ≤
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).prob (CutWitnessWithin G δ β err upper cap allowed U T))) := by
  let κ := fun U : Finset V => (subsetBernoulli U q).joint (neighborCopyLaw G)
  have hh := FiniteLaw.witness_transfer (bernoulliSubset p) κ
    (BadCutWithin G δ β upper allowed)
    (fun U x => CutWitnessWithin G δ β err upper cap allowed U x.1 x.2)
    hω0 (fun U hU => by
      obtain ⟨hupper,hdeg,A,hA,hallowed⟩ := hU
      rw [FiniteLaw.prob_joint]
      apply hω.trans
      apply (neighborCopy_fixed_uniform_witness G U A q hδ hmark herr hdeg hupper hcap hA).trans
      apply FiniteLaw.expect_mono
      intro T
      apply FiniteLaw.prob_mono
      intro ξ hξ
      exact ⟨hupper,hdeg,A,hA,hallowed,hξ⟩)
  simpa only [κ,FiniteLaw.prob_joint] using hh

end
end Cycle13
