import Cycle12.FixedWeakMajorityWitness
import Cycle12.WeakCutWitness

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def FixedRestrictedCutFailure (G : SimpleGraph V) (D : Finset V) (N : ℕ)
    (z dm beta eta : ℝ) (U : Finset V) : Prop :=
  U⊆D ∧ U.card=N ∧ (∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ)) ∧
    ∃ A⊆U, A.Nonempty ∧ 2*A.card ≤ U.card ∧ (A.card:ℝ) ≤ eta*U.card ∧
      ((G.interedges A (U\A)).card:ℝ) < beta*z*A.card

def FixedRestrictedMajorityWitness (G : SimpleGraph V) (D U T : Finset V)
    (xi : V → Finset V) (t : ℕ) (z dm beta err eta q : ℝ) : Prop :=
  ∃ A⊆U, A.Nonempty ∧ 2*A.card ≤ U.card ∧ (A.card:ℝ) ≤ eta*U.card ∧
    (dm-beta)*z < (A.card:ℝ) ∧
    let B := fixedMajorityInSample D U A (T,xi)
    B.Nonempty ∧ (U\B).Nonempty ∧
    ((A ∆ B).card:ℝ) ≤ (err+2*beta)/dm*A.card ∧
    (1-(err+2*beta)/dm)*A.card ≤ min (B.card:ℝ) (U\B).card ∧
    (B.card:ℝ) ≤ (1+(err+2*beta)/dm)*A.card ∧
    ((G.interedges B (U\B)).card:ℝ) ≤ (beta+err)*z*A.card ∧
    ((T∩A).card:ℝ) ≤ (exp 1-1)*((t:ℝ)/U.card)*A.card+q

/-- Transfer from arbitrary restricted bad cuts. The chosen cut remains
restricted, and is never replaced by a globally stable minimizer. -/
theorem fixed_restricted_bad_cut_transfer (G : SimpleGraph V) (D : Finset V)
    {N t : ℕ} (ht : t ≤ N) {z dm beta err eta lambda K q omega : ℝ}
    (hz : 0 < z) (hdm : 0 < dm) (herr : 0 < err) (hc : (err+2*beta)/dm < 1)
    (hdelta : 2 < dm*z) (hlambda : 3 ≤ lambda)
    (hmean : lambda ≤ ((t:ℝ)/N)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (homega0 : 0 ≤ omega)
    (homega : omega ≤ 1-(2*K*beta+dm*exp (-lambda))/err-exp (-q)) :
    omega*(fixedSizeLaw D N).prob (FixedRestrictedCutFailure G D N z dm beta eta) ≤
      (fixedMarkedExperiment D N t (fixedMajorityLaw G)).prob (fun x =>
        FixedRestrictedMajorityWitness G D x.1 x.2.1 x.2.2 t z dm beta err eta q) := by
  have hh := FiniteLaw.witness_transfer (fixedSizeLaw D N)
    (fun U => fixedMajorityExperiment G U t)
    (FixedRestrictedCutFailure G D N z dm beta eta)
    (fun U x => FixedRestrictedMajorityWitness G D U x.1 x.2 t z dm beta err eta q)
    homega0 (fun U hU => by
      obtain ⟨hUD,hcard,hdeg,A,hAU,hAn,hsmall,hsize,hbad⟩ := hU
      have hw := fixed_weak_majority_budget_probability G D U A hUD hAU hAn
        (by rwa [hcard] : t ≤ U.card) hz hdm herr hdelta hdeg hlambda
        (by simpa only [hcard] using hmean) hK hpure hmixed (q:=q) hbad.le
      apply homega.trans (hw.trans _)
      apply FiniteLaw.prob_mono
      intro x hx
      have hg := weak_cut_witness_geometry G U A (fixedMajorityInSample D U A x)
        hAU inter_subset_left hAn hsmall hz hdm hc hdeg hbad hx.1
      exact ⟨A,hAU,hAn,hsmall,hsize,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,
        hg.2.2.2.2.1,hg.2.2.2.2.2.1,hg.2.2.2.2.2.2,hx.2⟩)
  rw [fixed_marked_experiment_prob D N t (fixedMajorityLaw G)
    (fun U T xi => FixedRestrictedMajorityWitness G D U T xi t z dm beta err eta q)]
  simpa only [fixedMajorityExperiment,FiniteLaw.prob_joint] using hh

end
end Cycle12
