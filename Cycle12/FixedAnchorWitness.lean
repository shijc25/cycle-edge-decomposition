import Cycle12.FixedAnchorMeans
import Cycle12.Foundations.TwoWeightWitness

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_anchor_majority_witness_probability (G : SimpleGraph V) (U X C : Finset V)
    (hU : U.Nonempty) {k : ℕ} (hk : k ≤ U.card)
    {z dm beta L lambda K : ℝ} (hz : 0 < z) (hdm : 0 < dm) (hb : 0 < beta)
    (hdelta : 2 < dm*z) (hdeg : ∀ v, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hlambda : 3 ≤ lambda) (hmean : lambda ≤ ((k:ℝ)/U.card)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    {ew miss Kfull : ℝ} (hew : 0 < ew) (hmiss : 0 < miss) (hL : 0 < L)
    (hKfull : 1 ≤ Kfull) (hcor : majorityCorrection (dm*z)*(9/8) ≤ Kfull)
    (hexp : SampleCutExpansion G U (beta*z)) (hbad : BadAnchorCut G U X C L) :
    1-(2*K+(dm/beta)*exp (-lambda))/ew-(Kfull*L/(dm*z)+exp (-lambda))/miss ≤
      (fixedMajorityExperiment G U k).prob (fun x =>
        jointCutError G U C (fixedMajorityInSample univ U C x) ≤ ew*L*X.card ∧
        fixedOutsideMajorityMisses X C x ≤ miss*X.card) := by
  let mu := fixedMajorityExperiment G U k
  let W := fun x => jointCutError G U C (fixedMajorityInSample univ U C x)
  let Z := fixedOutsideMajorityMisses X C
  have hx := hbad.2.2.2.1
  have hs : 0 < ew*L*X.card := mul_pos (mul_pos hew hL) hx
  have ht : 0 < miss*X.card := mul_pos hmiss hx
  have hW : mu.expect W ≤ (2*K+(dm/beta)*exp (-lambda))*L*X.card :=
    fixed_anchor_majority_cost_expect G U X C hU hk hz hdm hb hdelta
      (fun v _ => hdeg v) hlambda hmean hK hpure hmixed hexp hbad
  have hZ : mu.expect Z ≤ (Kfull*L/(dm*z)+exp (-lambda))*X.card :=
    fixed_anchor_majority_misses_expect G U X C hU hk hdelta (fun v _ => hdeg v)
      hmean hKfull hcor hbad
  have hwdiv : mu.expect W/(ew*L*X.card) ≤ (2*K+(dm/beta)*exp (-lambda))/ew := by
    apply (div_le_div_of_nonneg_right hW hs.le).trans_eq
    field_simp [hew.ne',hL.ne',hx.ne']
  have hzdiv : mu.expect Z/(miss*X.card) ≤ (Kfull*L/(dm*z)+exp (-lambda))/miss := by
    apply (div_le_div_of_nonneg_right hZ ht.le).trans_eq
    field_simp [hmiss.ne',hx.ne']
  have hg := mu.prob_good_two_weights W Z (fun _ => False)
    (fun _ => joint_cut_error_nonneg G U C _) (fun _ => Nat.cast_nonneg _) hs ht
  have hf : mu.prob (fun _ => False)=0 := by
    simp only [FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
  rw [hf] at hg
  simp only [not_false_eq_true,and_true,sub_zero] at hg
  linarith only [hg,hwdiv,hzdiv]

/-- The two crossing incidences must be restored when passing from joint
cost to the number of wrongly classified sampled vertices. -/
theorem anchor_joint_error_geometry (G : SimpleGraph V) (U X C B : Finset V)
    (hB : B⊆U) {L ew : ℝ} (hbad : BadAnchorCut G U X C L)
    (herror : jointCutError G U C B ≤ ew*L*X.card) :
    sampledErrorWeight G U C B ≤ (ew+2)*L*X.card ∧
      ((G.interedges B (U\B)).card:ℝ) ≤ (1+ew)*L*X.card := by
  have hnon : (0:ℝ) ≤ (G.interedges X (U\C)).card := Nat.cast_nonneg _
  have hc : ((G.interedges C (U\C)).card:ℝ) ≤ L*X.card := by
    linarith only [hnon,hbad.2.2.2.2]
  have hd := joint_cut_error_to_degree_error G U C B hbad.2.1 hB
  have he := joint_cut_perturbation G U C B hbad.2.1 hB
  constructor <;> nlinarith only [hd,he,hc,herror]

end
end Cycle12
