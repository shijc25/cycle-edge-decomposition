import Cycle12.FixedMajorityWitness
import Cycle12.WeakCutError

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The tau=0 joint charge gives the original same-side error budget for
an arbitrary restricted cut. No global stability assumption is introduced. -/
theorem fixed_weak_majority_budget_probability (G : SimpleGraph V) (D U A : Finset V)
    (hUD : U⊆D) (hA : A⊆U) (hAn : A.Nonempty) {k : ℕ} (hk : k ≤ U.card)
    {z dm beta err lambda K q : ℝ} (hz : 0 < z) (hdm : 0 < dm) (herr : 0 < err)
    (hdelta : 2 < dm*z) (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hlambda : 3 ≤ lambda) (hmean : lambda ≤ ((k:ℝ)/U.card)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (hbad : ((G.interedges A (U\A)).card:ℝ) ≤ beta*z*A.card) :
    1-(2*K*beta+dm*exp (-lambda))/err-exp (-q) ≤
      (fixedMajorityExperiment G U k).prob (fun x =>
        jointCutError G U A (fixedMajorityInSample D U A x) ≤ err*z*A.card ∧
        ((x.1∩A).card:ℝ) ≤ (exp 1-1)*((k:ℝ)/U.card)*A.card+q) := by
  have hU : U.Nonempty := hAn.mono hA
  have he := fixed_majority_joint_cost_mean G D U A hUD hU hA hk hz hdm
    (tau:=0) (by norm_num) hdelta hdeg hlambda hmean hK
    (by simpa only [zero_div,add_zero] using hpure)
    (by simpa only [zero_div,add_zero] using hmixed)
  simp only [zero_mul,add_zero] at he
  rw [neg_mul] at he
  have hcut := mul_le_mul_of_nonneg_left hbad (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hK)
  have hexp := exp_le_exp.mpr (neg_le_neg hmean)
  have htail := mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (mul_pos hdm hz).le (Nat.cast_nonneg A.card))
  have hM : (fixedMajorityExperiment G U k).expect
      (fun x => jointCutError G U A (fixedMajorityInSample D U A x)) ≤
        (2*K*beta+dm*exp (-lambda))*z*A.card := by
    nlinarith only [he,hcut,htail]
  let bad := fun x : Finset V×(V → Finset V) =>
    (exp 1-1)*((k:ℝ)/U.card)*A.card+q < ((x.1∩A).card:ℝ)
  have hb : (fixedMajorityExperiment G U k).prob bad ≤ exp (-q) := by
    dsimp only [bad]
    rw [fixedMajorityExperiment,FiniteLaw.prob_joint_fst (fixedSizeLaw U k) (fixedMajorityLaw G)
      (fun T : Finset V => (exp 1-1)*((k:ℝ)/U.card)*A.card+q < ((T∩A).card:ℝ))]
    exact fixed_mark_minority_tail U A hU hA hk q
  have ha : (0:ℝ) < A.card := by exact_mod_cast hAn.card_pos
  have hbudget : 0 < err*z*A.card := mul_pos (mul_pos herr hz) ha
  have hw := (fixedMajorityExperiment G U k).prob_good_weight
    (fun x => jointCutError G U A (fixedMajorityInSample D U A x)) bad
    (fun x => joint_cut_error_nonneg G U A _) hbudget
  have hfrac := div_le_div_of_nonneg_right hM hbudget.le
  have hid : (2*K*beta+dm*exp (-lambda))*z*A.card/(err*z*A.card)=
      (2*K*beta+dm*exp (-lambda))/err := by field_simp
  rw [hid] at hfrac
  simp only [bad,not_lt] at hw
  linarith only [hw,hfrac,hb]

end
end Cycle12
