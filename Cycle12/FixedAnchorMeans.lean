import Cycle12.FixedOutsideMajority
import Cycle12.WeakCutError
import Cycle12.Foundations.AnchorGeometry

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Joint cost on the sampled side of an arbitrary bad anchor cut.
Only sample expansion, not stable-minimizer inequalities, is used. -/
theorem fixed_anchor_majority_cost_expect (G : SimpleGraph V) (U X C : Finset V)
    (hU : U.Nonempty) {k : ℕ} (hk : k ≤ U.card)
    {z dm beta L lambda K : ℝ} (hz : 0 < z) (hdm : 0 < dm) (hb : 0 < beta)
    (hdelta : 2 < dm*z) (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hlambda : 3 ≤ lambda) (hmean : lambda ≤ ((k:ℝ)/U.card)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (hexp : SampleCutExpansion G U (beta*z)) (hbad : BadAnchorCut G U X C L) :
    (fixedMajorityExperiment G U k).expect (fun x =>
      jointCutError G U C (fixedMajorityInSample univ U C x)) ≤
      (2*K+(dm/beta)*exp (-lambda))*L*X.card := by
  have he := fixed_majority_joint_cost_mean G univ U C (subset_univ U) hU hbad.2.1 hk
    hz hdm (tau:=0) (by norm_num) hdelta hdeg hlambda hmean hK
    (by simpa only [zero_div,add_zero] using hpure)
    (by simpa only [zero_div,add_zero] using hmixed)
  simp only [zero_mul,add_zero] at he
  rw [neg_mul] at he
  have hcut := hexp C hbad.2.1 hbad.2.2.1
  have hnon : (0:ℝ) ≤ (G.interedges X (U\C)).card := Nat.cast_nonneg _
  have hcutmax : ((G.interedges C (U\C)).card:ℝ) ≤ L*X.card := by
    linarith only [hbad.2.2.2.2,hnon]
  have hC : (C.card:ℝ) ≤ L*X.card/(beta*z) :=
    (le_div_iff₀ (mul_pos hb hz)).mpr (by nlinarith only [hcut,hcutmax])
  have ht := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hmean))
    (mul_nonneg (mul_pos hdm hz).le (Nat.cast_nonneg C.card))
  have hCc := mul_le_mul_of_nonneg_left hC (mul_nonneg (mul_pos hdm hz).le (exp_pos (-lambda)).le)
  have hid : (dm*z*exp (-lambda))*(L*X.card/(beta*z))=
      (dm/beta)*exp (-lambda)*L*X.card := by field_simp
  rw [hid] at hCc
  have hkcut := mul_le_mul_of_nonneg_left hcutmax (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hK)
  nlinarith only [he,ht,hCc,hkcut]

theorem fixed_anchor_majority_misses_expect (G : SimpleGraph V) (U X C : Finset V)
    (hU : U.Nonempty) {k : ℕ} (hk : k ≤ U.card)
    {delta L lambda Kfull : ℝ} (hdelta : 2 < delta)
    (hdeg : ∀ v∈X, delta ≤ ((neighborsIn G v U).card:ℝ))
    (hmean : lambda ≤ ((k:ℝ)/U.card)*delta)
    (hK : 1 ≤ Kfull) (hcor : majorityCorrection delta*(9/8) ≤ Kfull)
    (hbad : BadAnchorCut G U X C L) :
    (fixedMajorityExperiment G U k).expect (fixedOutsideMajorityMisses X C) ≤
      (Kfull*L/delta+exp (-lambda))*X.card := by
  have hh := fixed_outside_majority_misses_expect G U X C hU hbad.1 hk hdelta hdeg hmean hK hcor
  have hnon : (0:ℝ) ≤ (G.interedges C (U\C)).card := Nat.cast_nonneg _
  have hcost : ((G.interedges X (U\C)).card:ℝ) ≤ L*X.card := by
    linarith only [hnon,hbad.2.2.2.2]
  have hbound := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcost (show 0 ≤ Kfull by linarith only [hK]))
    (show 0 ≤ delta by linarith only [hdelta])
  calc
    _ ≤ Kfull*((G.interedges X (U\C)).card:ℝ)/delta+exp (-lambda)*X.card := hh
    _ ≤ Kfull*(L*X.card)/delta+exp (-lambda)*X.card := add_le_add hbound le_rfl
    _ = _ := by ring

end
end Cycle12
