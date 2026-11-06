import Cycle12.Foundations.NeighborWitnessProbability

/-! A bad cut selected after observing U is converted to a witness of
the original experiment. The auxiliary law depends only on T. -/
namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def BadSampleCut (G : SimpleGraph V) (U A : Finset V) (β : ℝ) : Prop :=
  A⊆U ∧ 0<(A.card:ℝ) ∧ 2*A.card≤U.card ∧
    ((G.interedges A (U\A)).card:ℝ)≤β*A.card

def BadCutSample (G : SimpleGraph V) (δ β upper : ℝ) (U : Finset V) : Prop :=
  (U.card:ℝ)≤upper ∧ (∀ v∈U, δ≤((neighborsIn G v U).card:ℝ)) ∧
    ∃ A, BadSampleCut G U A β

def BadCutCopyWitness (G : SimpleGraph V) (β err cap : ℝ) (U T : Finset V)
    (ξ : V→Option V) : Prop :=
  ∃ A, BadSampleCut G U A β ∧
    sampledErrorWeight G U A (U∩copiedSide T ξ (A∩T))≤err*A.card ∧ (T.card:ℝ)≤cap

theorem neighborCopy_uniform_witness (G : SimpleGraph V) (U A : Finset V)
    (q : unitInterval) {δ β err upper cap : ℝ}
    (hδ : 0<δ) (hmark : 1≤(q:ℝ)*δ) (herr : 0<err)
    (hdeg : ∀ v∈U, δ≤((neighborsIn G v U).card:ℝ))
    (hupper : (U.card:ℝ)≤upper) (hcap : (q:ℝ)*upper≤cap)
    (hA : BadSampleCut G U A β) :
    1-(2*β+δ*exp (-(q:ℝ)*δ))/err-exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) ≤
    (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).prob
      (BadCutCopyWitness G β err cap U T)) := by
  have hq : 0<(q:ℝ) := by nlinarith [q.2.1]
  have hU : 0<(U.card:ℝ) := hA.2.1.trans_le (by exact_mod_cast card_le_card hA.1)
  have hμ : 0<(q:ℝ)*U.card := mul_pos hq hU
  have hμmax := mul_le_mul_of_nonneg_left hupper q.2.1
  have hcapU : (q:ℝ)*U.card≤cap := hμmax.trans hcap
  have hcap0 : 0<cap := hμ.trans_le hcapU
  have hh := neighborCopy_cut_witness G U A hA.1 hA.2.1 q hδ hmark hdeg herr hA.2.2.2 hμ hcapU
  have htail : exp (-(cap-(q:ℝ)*U.card)^2/(2*cap)) ≤
      exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) := by
    apply exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num : (0:ℝ)<2) hcap0)).mpr
    nlinarith
  apply le_trans (show 1-(2*β+δ*exp (-(q:ℝ)*δ))/err-exp (-(cap-(q:ℝ)*upper)^2/(2*cap)) ≤
    1-(2*β+δ*exp (-(q:ℝ)*δ))/err-exp (-(cap-(q:ℝ)*U.card)^2/(2*cap)) by linarith)
  apply hh.trans
  apply FiniteLaw.expect_mono
  intro T
  apply FiniteLaw.prob_mono
  intro ξ hξ
  exact ⟨A,hA,hξ⟩

theorem bad_cut_witness_transfer (G : SimpleGraph V) (p q : unitInterval)
    {δ β err upper cap ω : ℝ} (hδ : 0<δ) (hmark : 1≤(q:ℝ)*δ)
    (herr : 0<err) (hcap : (q:ℝ)*upper≤cap) (hω0 : 0≤ω)
    (hω : ω≤1-(2*β+δ*exp (-(q:ℝ)*δ))/err-exp (-(cap-(q:ℝ)*upper)^2/(2*cap))) :
    ω*(bernoulliSubset p).prob (BadCutSample G δ β upper) ≤
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).prob (BadCutCopyWitness G β err cap U T))) := by
  let κ := fun U : Finset V => (subsetBernoulli U q).joint (neighborCopyLaw G)
  have hh := FiniteLaw.witness_transfer (bernoulliSubset p) κ
    (BadCutSample G δ β upper) (fun U x => BadCutCopyWitness G β err cap U x.1 x.2)
    hω0 (fun U hU => by
      obtain ⟨hupper,hdeg,A,hA⟩ := hU
      rw [FiniteLaw.prob_joint]
      exact hω.trans (neighborCopy_uniform_witness G U A q hδ hmark herr hdeg hupper hcap hA))
  simp only [κ,FiniteLaw.prob_joint] at hh
  exact hh

end
end Cycle13
