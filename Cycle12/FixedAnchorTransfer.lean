import Cycle12.FixedAnchorWitness
import Cycle12.FixedMarkedExperiment

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def FixedAnchorFailure (G : SimpleGraph V) (N : ℕ) (z dm beta L : ℝ) (U : Finset V) : Prop :=
  U.card=N ∧ (∀ v, dm*z ≤ ((neighborsIn G v U).card:ℝ)) ∧
    SampleCutExpansion G U (beta*z) ∧ ∃ X C, BadAnchorCut G U X C L

def FixedAnchorMajorityWitness (G : SimpleGraph V) (N : ℕ) (z dm beta L ew miss : ℝ)
    (U T : Finset V) (xi : V → Finset V) : Prop :=
  U.card=N ∧ (∀ v, dm*z ≤ ((neighborsIn G v U).card:ℝ)) ∧
    SampleCutExpansion G U (beta*z) ∧ ∃ X C, BadAnchorCut G U X C L ∧
      jointCutError G U C (fixedMajorityInSample univ U C (T,xi)) ≤ ew*L*X.card ∧
      fixedOutsideMajorityMisses X C (T,xi) ≤ miss*X.card

theorem fixed_anchor_bad_cut_transfer (G : SimpleGraph V) {N t : ℕ}
    (hN : 0 < N) (ht : t ≤ N) {z dm beta L voteLambda K ew miss Kfull omega : ℝ}
    (hz : 0 < z) (hdm : 0 < dm) (hb : 0 < beta) (hL : 0 < L)
    (hdelta : 2 < dm*z) (hlambda : 3 ≤ voteLambda)
    (hmean : voteLambda ≤ ((t:ℝ)/N)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1-rho)*(min 1 (poissonTailTwo voteLambda)+
        (1-min 1 (poissonTailTwo voteLambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (hew : 0 < ew) (hmiss : 0 < miss) (hKfull : 1 ≤ Kfull)
    (hcor : majorityCorrection (dm*z)*(9/8) ≤ Kfull) (homega0 : 0 ≤ omega)
    (homega : omega ≤ 1-(2*K+(dm/beta)*exp (-voteLambda))/ew-
      (Kfull*L/(dm*z)+exp (-voteLambda))/miss) :
    omega*(fixedSizeLaw (univ:Finset V) N).prob (FixedAnchorFailure G N z dm beta L) ≤
      (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob (fun x =>
        FixedAnchorMajorityWitness G N z dm beta L ew miss x.1 x.2.1 x.2.2) := by
  have hh := FiniteLaw.witness_transfer (fixedSizeLaw (univ:Finset V) N)
    (fun U => fixedMajorityExperiment G U t) (FixedAnchorFailure G N z dm beta L)
    (fun U x => FixedAnchorMajorityWitness G N z dm beta L ew miss U x.1 x.2)
    homega0 (fun U hU => by
      obtain ⟨hcard,hdeg,hexp,X,C,hbad⟩ := hU
      have hUn : U.Nonempty := card_pos.mp (by rwa [hcard])
      have hw := fixed_anchor_majority_witness_probability G U X C hUn
        (by rwa [hcard] : t ≤ U.card) hz hdm hb hdelta hdeg hlambda
        (by simpa only [hcard] using hmean) hK hpure hmixed hew hmiss hL hKfull hcor hexp hbad
      apply homega.trans (hw.trans _)
      exact FiniteLaw.prob_mono _ (fun x hx => ⟨hcard,hdeg,hexp,X,C,hbad,hx⟩))
  rw [fixed_marked_experiment_prob (univ:Finset V) N t (fixedMajorityLaw G)
    (fun U T xi => FixedAnchorMajorityWitness G N z dm beta L ew miss U T xi)]
  simpa only [fixedMajorityExperiment,FiniteLaw.prob_joint] using hh

end
end Cycle12
