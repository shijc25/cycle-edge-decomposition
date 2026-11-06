import Cycle12.FixedGlobalWitnessUpper
import Cycle12.GlobalSplitPopulation
import Cycle12.FixedCutLabelTail

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Both label encodings apply to the same adaptive bad-cut witness. The
minority entropy is charged only below the predetermined population cut. -/
theorem fixed_global_split_witness_upper (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta tau q theta ell err nu rho cutoff etaSmall etaLarge : ℝ}
    (hz : 0 < z) (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm)
    (htheta : 0 < theta) (hscale : 0 < ell/theta) (hnu : 0 < nu)
    (hr : 0 < rho) (hrhalf : rho ≤ 1/2) (heS : 0 ≤ etaSmall) (heL : 0 ≤ etaLarge)
    (hnuBound : nu ≤
      (max (dm-tau) ((1-(tau-beta)/(tau+(dm-beta)/2))*(dm-beta))*z-err)/(ell/theta))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (hlabelBudget : (exp 1-1)*((t:ℝ)/N)*
      (((ell/theta)*cutoff+err)/(1-(tau-beta)/(tau+(dm-beta)/2)))+q ≤ rho*t)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    (lambda M fraction : Finset V → Finset V → (V → Finset V) → ℝ)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T p
        (lambda T A xi) (M T A xi) (fraction T A xi)
        (if ((fixedMajoritySmallSide T A xi).card:ℝ) ≤ cutoff then etaSmall else etaLarge) ∧
      tau*z*((ell/theta)*(fixedMajoritySmallSide T A xi).card+err) ≤
        fraction T A xi*(M T A xi*(p:ℝ)^2)) :
    (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob (fun x =>
      FixedGlobalStrongMajorityWitness G univ x.1 x.2.1 x.2.2 t z dm beta tau q) ≤
      2*exp (-theta*err)*(1+exp (theta-ell))^t+
        (exp ((t:ℝ)*binEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge) := by
  let eligible := fun (T A : Finset V) (xi : V → Finset V) =>
    nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ)
  let Ecount := fun x : Finset V×(Finset V×(V → Finset V)) =>
    fixedMajorityCountingFailure x.1 x.2.1 x.2.2 (ell/theta) err
  let Ecut := fun x : Finset V×(Finset V×(V → Finset V)) => ∃ A⊆x.2.1,
    ((A.card:ℝ) ≤ rho*t ∧ eligible x.2.1 A x.2.2 ∧
      ((fixedMajoritySmallSide x.2.1 A x.2.2).card:ℝ) ≤ cutoff ∧
      ((G.interedges (x.1∩fixedMajoritySmallSide x.2.1 A x.2.2)
        (x.1\fixedMajoritySmallSide x.2.1 A x.2.2)).card:ℝ) ≤
        fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2)) ∨
    (eligible x.2.1 A x.2.2 ∧ cutoff < ((fixedMajoritySmallSide x.2.1 A x.2.2).card:ℝ) ∧
      ((G.interedges (x.1∩fixedMajoritySmallSide x.2.1 A x.2.2)
        (x.1\fixedMajoritySmallSide x.2.1 A x.2.2)).card:ℝ) ≤
        fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2))
  have hcount : (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob Ecount ≤
      2*exp (-theta*err)*(1+exp (theta-ell))^t := by
    simpa only [Ecount,fixedMajorityCountingFailure,card_univ] using
      fixed_majority_two_colors_counting_failure G (univ:Finset V)
        (by simpa using hN) ht (by simpa using htD) htheta (by simpa using hmgf) (err:=err)
  have htail : (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob Ecut ≤
      exp ((t:ℝ)*binEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge := by
    exact fixed_marked_split_cut_bound G hN ht (fixedMajorityLaw G) fixedMajoritySmallSide
      lambda M fraction eligible p hp0 hp hmean hr hrhalf heS heL
      (fun T hT A hA xi hel => (hvalid T hT A hA xi hel).1)
  have hincl : (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob
      (fun x => FixedGlobalStrongMajorityWitness G univ x.1 x.2.1 x.2.2 t z dm beta tau q) ≤
      (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob (fun x => Ecount x ∨ Ecut x) := by
    apply FiniteLaw.prob_mono_support
    intro x hx hw
    by_cases hc : Ecount x
    · exact Or.inl hc
    · have hs := fixed_marked_experiment_support (univ:Finset V) (by simpa using hN) ht
        (fixedMajorityLaw G) x hx
      have hgood := fixed_majority_not_counting_failure x.1 x.2.1 x.2.2 hc
      obtain ⟨A,hA,hpop,hcut,hregime⟩ := strong_majority_split_witness G x.1 x.2.1 x.2.2 hs.2.1
        hz hb hbt hbd hscale hw hgood hlabelBudget
      have hel : eligible x.2.1 A x.2.2 := hnuBound.trans hpop
      have hcut' := hcut.trans (hvalid x.2.1 hs.2.2.2.1 A hA x.2.2 hel).2
      apply Or.inr
      refine ⟨A,hA,?_⟩
      rcases hregime with ⟨hsmall,hlabel⟩ | hlarge
      · exact Or.inl ⟨hlabel,hel,hsmall,hcut'⟩
      · exact Or.inr ⟨hel,hlarge,hcut'⟩
  exact hincl.trans (((fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob_union_le
    Ecount Ecut).trans (add_le_add hcount htail))

end
end Cycle12
