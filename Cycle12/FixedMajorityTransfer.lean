import Cycle12.FixedMajorityWitness
import Cycle12.FixedMajorityCounting

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def FixedExpansionFailure (G : SimpleGraph V) (D : Finset V) (N : ℕ)
    (z dm beta : ℝ) (U : Finset V) : Prop :=
  U⊆D ∧ U.card=N ∧ (∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ)) ∧
    ∃ S⊆U, ((G.interedges S (U\S)).card:ℝ)<beta*z*min (S.card:ℝ) (U\S).card

def FixedGlobalMajorityWitness (G : SimpleGraph V) (D U T : Finset V)
    (xi : V → Finset V) (t : ℕ) (z dm beta tau q : ℝ) : Prop :=
  ∃ A, A⊆U ∧ A.Nonempty ∧ 2*A.card ≤ U.card ∧
    let B := fixedMajorityInSample D U A (T,xi)
    B.Nonempty ∧ (U\B).Nonempty ∧
    ((G.interedges B (U\B)).card:ℝ)<tau*z*min (B.card:ℝ) (U\B).card ∧
    (dm-tau)*z < min (B.card:ℝ) (U\B).card ∧
    ((A ∆ B).card:ℝ) ≤ (tau-beta)/(tau+(dm-beta)/2)*A.card ∧
    ((T∩A).card:ℝ) ≤ (exp 1-1)*((t:ℝ)/U.card)*A.card+q

/-- A cut selected after observing the sample is transferred into the
original fixed sample/mark/majority experiment. The auxiliary choices never
inspect the sample beyond its unlabelled marked set. -/
theorem fixed_majority_bad_cut_transfer (G : SimpleGraph V) (D : Finset V)
    {N t : ℕ} (ht : t ≤ N) {z dm beta tau lambda K q omega : ℝ}
    (hz : 0<z) (hdm : 0<dm) (hbeta : 0<beta) (hbt : beta<tau) (hbd : beta<dm)
    (hdelta : 2<dm*z) (hlambda : 3 ≤ lambda)
    (hmean : lambda ≤ ((t:ℝ)/N)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1+tau/dm-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1+tau/dm-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (homega0 : 0 ≤ omega)
    (homega : omega ≤ 1-(2*K*beta+(dm+tau)*exp (-lambda))/(tau-beta)-exp (-q)) :
    omega*(fixedSizeLaw D N).prob (FixedExpansionFailure G D N z dm beta) ≤
      (fixedMarkedExperiment D N t (fixedMajorityLaw G)).prob (fun x =>
        FixedGlobalMajorityWitness G D x.1 x.2.1 x.2.2 t z dm beta tau q) := by
  have hh := FiniteLaw.witness_transfer (fixedSizeLaw D N)
    (fun U => fixedMajorityExperiment G U t)
    (FixedExpansionFailure G D N z dm beta)
    (fun U x => FixedGlobalMajorityWitness G D U x.1 x.2 t z dm beta tau q)
    homega0 (fun U hU => by
      obtain ⟨hUD,hcard,hdeg,S,hS,hbadS⟩ := hU
      obtain ⟨A,hstable,hAn,_,hsmall,hbad⟩ := exists_stable_bad_cut G U S hS hbadS
      have hw := fixed_majority_stable_witness_probability G D U A hUD hAn hsmall
        (by rwa [hcard] : t ≤ U.card) hz hdm hbeta hbt hbd hstable hdelta hdeg
        hlambda (by simpa only [hcard] using hmean) hK hpure hmixed (q:=q) hbad
      apply homega.trans (hw.trans _)
      apply FiniteLaw.prob_mono
      intro x hx
      exact ⟨A,hstable.1,hAn,hsmall,hx⟩)
  rw [fixed_marked_experiment_prob D N t (fixedMajorityLaw G)
    (fun U T xi => FixedGlobalMajorityWitness G D U T xi t z dm beta tau q)]
  simpa only [fixedMajorityExperiment,FiniteLaw.prob_joint] using hh

end
end Cycle12
