import Cycle12.FixedMajorityJointCost
import Cycle12.FixedSampleTails
import Cycle12.JointStableWitness

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A single joint Markov event for the actual fixed-size experiment,
including the original minority-label exception. -/
theorem fixed_majority_joint_budget_probability (G : SimpleGraph V) (D U A : Finset V)
    (hUD : U⊆D) (hA : A⊆U) (hAn : A.Nonempty) {k : ℕ} (hk : k ≤ U.card)
    {z dm beta tau lambda K q : ℝ} (hz : 0<z) (hdm : 0<dm)
    (hbeta : 0<beta) (hbt : beta<tau) (hdelta : 2<dm*z)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hlambda : 3 ≤ lambda) (hmean : lambda ≤ ((k:ℝ)/U.card)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1+tau/dm-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1+tau/dm-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (hbad : ((G.interedges A (U\A)).card:ℝ) ≤ beta*z*A.card) :
    1-(2*K*beta+(dm+tau)*exp (-lambda))/(tau-beta)-exp (-q) ≤
      (fixedMajorityExperiment G U k).prob (fun x =>
        jointCutError G U A (fixedMajorityInSample D U A x)+
          tau*z*(A ∆ fixedMajorityInSample D U A x).card ≤ (tau-beta)*z*A.card ∧
        ((x.1∩A).card:ℝ) ≤ (exp 1-1)*((k:ℝ)/U.card)*A.card+q) := by
  have hU : U.Nonempty := hAn.mono hA
  have htau : 0 ≤ tau := (hbeta.trans hbt).le
  have he := fixed_majority_joint_cost_mean G D U A hUD hU hA hk hz hdm htau hdelta hdeg
    hlambda hmean hK hpure hmixed
  have hM : (fixedMajorityExperiment G U k).expect (fun x =>
      jointCutError G U A (fixedMajorityInSample D U A x)+
        tau*z*(A ∆ fixedMajorityInSample D U A x).card) ≤
      (2*K*beta+(dm+tau)*exp (-lambda))*z*A.card := by
    have hcut := mul_le_mul_of_nonneg_left hbad (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hK)
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hmean)
    have htail := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg (add_nonneg (mul_pos hdm hz).le (mul_nonneg htau hz.le)) (Nat.cast_nonneg A.card))
    rw [neg_mul] at he
    nlinarith only [he,hcut,htail]
  let bad : Finset V×(V → Finset V) → Prop := fun x =>
    (exp 1-1)*((k:ℝ)/U.card)*A.card+q < ((x.1∩A).card:ℝ)
  have hb : (fixedMajorityExperiment G U k).prob bad ≤ exp (-q) := by
    dsimp only [bad]
    rw [fixedMajorityExperiment,FiniteLaw.prob_joint_fst (fixedSizeLaw U k) (fixedMajorityLaw G)
      (fun T : Finset V => (exp 1-1)*((k:ℝ)/U.card)*A.card+q < ((T∩A).card:ℝ))]
    exact fixed_mark_minority_tail U A hU hA hk q
  have hw := joint_cut_witness_probability (fixedMajorityExperiment G U k) G U A
    (fixedMajorityInSample D U A) bad hz hbeta hbt hAn hM
  have hcard : (A.card:ℝ)≠0 := ne_of_gt (by exact_mod_cast hAn.card_pos)
  have hrat : (2*K*beta+(dm+tau)*exp (-lambda))*z*A.card/((tau-beta)*z*A.card)=
      (2*K*beta+(dm+tau)*exp (-lambda))/(tau-beta) := by
    have hden := (sub_pos.mpr hbt).ne'
    field_simp
  rw [hrat] at hw
  simp only [bad,not_lt] at hw
  linarith only [hw,hb]

theorem fixed_majority_stable_witness_probability (G : SimpleGraph V) (D U A : Finset V)
    (hUD : U⊆D) (hAn : A.Nonempty) (hsmall : 2*A.card ≤ U.card)
    {k : ℕ} (hk : k ≤ U.card) {z dm beta tau lambda K q : ℝ}
    (hz : 0<z) (hdm : 0<dm) (hbeta : 0<beta) (hbt : beta<tau) (hbd : beta<dm)
    (hstable : IsStableCut G U A (beta*z)) (hdelta : 2<dm*z)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hlambda : 3 ≤ lambda) (hmean : lambda ≤ ((k:ℝ)/U.card)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1+tau/dm-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1+tau/dm-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (hbad : ((G.interedges A (U\A)).card:ℝ)<beta*z*A.card) :
    1-(2*K*beta+(dm+tau)*exp (-lambda))/(tau-beta)-exp (-q) ≤
      (fixedMajorityExperiment G U k).prob (fun x =>
        let B := fixedMajorityInSample D U A x
        B.Nonempty ∧ (U\B).Nonempty ∧
        ((G.interedges B (U\B)).card:ℝ)<tau*z*min (B.card:ℝ) (U\B).card ∧
        (dm-tau)*z < min (B.card:ℝ) (U\B).card ∧
        ((A ∆ B).card:ℝ) ≤ (tau-beta)/(tau+(dm-beta)/2)*A.card ∧
        ((x.1∩A).card:ℝ) ≤ (exp 1-1)*((k:ℝ)/U.card)*A.card+q) := by
  have hh := fixed_majority_joint_budget_probability G D U A hUD hstable.1 hAn hk hz hdm
    hbeta hbt hdelta hdeg hlambda hmean hK hpure hmixed (q:=q) hbad.le
  apply hh.trans
  apply FiniteLaw.prob_mono
  intro x hx
  have hw := stable_joint_cut_witness G U A (fixedMajorityInSample D U A x)
    hz hbeta hbt hbd hstable inter_subset_left hAn hsmall hdeg hbad hx.1
  exact ⟨hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2,hx.2⟩

end
end Cycle12
