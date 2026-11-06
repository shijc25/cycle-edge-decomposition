import Cycle12.FixedGlobalSplitFailure
import Cycle12.CappedLabelEntropy

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

/-- Extends the two label regimes to every positive proportion. Above one half, the entire powerset is charged through cappedLabelEntropy. -/
theorem fixed_marked_two_label_regimes_capped (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (Esmall Elarge : Finset V → Finset V → Ξ → Finset V → Prop) {rho etaSmall etaLarge : ℝ}
    (hr : 0 < rho) (hetaSmall : 0 ≤ etaSmall)
    (hsmall : ∀ T⊆D, T.card=t → ∀ xi A, A⊆T → (A.card:ℝ) ≤ rho*t →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => Esmall (T∪R) T xi A) ≤ etaSmall)
    (hlarge : ∀ T⊆D, T.card=t → ∀ xi A, A⊆T →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => Elarge (T∪R) T xi A) ≤ etaLarge) :
    (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
      ((A.card:ℝ) ≤ rho*t ∧ Esmall x.1 x.2.1 x.2.2 A) ∨ Elarge x.1 x.2.1 x.2.2 A) ≤
      exp ((t:ℝ)*cappedLabelEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge := by
  let Fsmall := fun x : Finset V×(Finset V×Ξ) =>
    ∃ A⊆x.2.1, (A.card:ℝ) ≤ rho*t ∧ Esmall x.1 x.2.1 x.2.2 A
  let Flarge := fun x : Finset V×(Finset V×Ξ) => ∃ A⊆x.2.1, Elarge x.1 x.2.1 x.2.2 A
  have hs := fixed_marked_capped_minority_bound D hN ht kap Esmall hr hetaSmall hsmall
  have hl := fixed_marked_uniform_label_bound D hN ht kap Elarge hlarge
  have hincl : (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
      ((A.card:ℝ) ≤ rho*t ∧ Esmall x.1 x.2.1 x.2.2 A) ∨ Elarge x.1 x.2.1 x.2.2 A) ≤
      (fixedMarkedExperiment D N t kap).prob (fun x => Fsmall x ∨ Flarge x) := by
    apply FiniteLaw.prob_mono
    rintro x ⟨A,hA,h | h⟩
    · exact Or.inl ⟨A,hA,h⟩
    · exact Or.inr ⟨A,hA,h⟩
  exact hincl.trans (((fixedMarkedExperiment D N t kap).prob_union_le Fsmall Flarge).trans
    (add_le_add hs hl))


theorem fixed_marked_split_cut_bound_capped (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (S : Finset V → Finset V → Ξ → Finset V)
    (lambda M fraction : Finset V → Finset V → Ξ → ℝ)
    (eligible : Finset V → Finset V → Ξ → Prop)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    {rho cutoff etaSmall etaLarge : ℝ} (hr : 0 < rho) 
    (heS : 0 ≤ etaSmall) (heL : 0 ≤ etaLarge)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi, eligible T A xi →
      RoundedCutLabelValid G (S T A xi) T p (lambda T A xi) (M T A xi) (fraction T A xi)
        (if ((S T A xi).card:ℝ) ≤ cutoff then etaSmall else etaLarge)) :
    (fixedMarkedExperiment (univ:Finset V) N t kap).prob (fun x => ∃ A⊆x.2.1,
      ((A.card:ℝ) ≤ rho*t ∧ eligible x.2.1 A x.2.2 ∧ ((S x.2.1 A x.2.2).card:ℝ) ≤ cutoff ∧
        ((G.interedges (x.1∩S x.2.1 A x.2.2) (x.1\S x.2.1 A x.2.2)).card:ℝ) ≤
          fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2)) ∨
      (eligible x.2.1 A x.2.2 ∧ cutoff < ((S x.2.1 A x.2.2).card:ℝ) ∧
        ((G.interedges (x.1∩S x.2.1 A x.2.2) (x.1\S x.2.1 A x.2.2)).card:ℝ) ≤
          fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2))) ≤
      exp ((t:ℝ)*cappedLabelEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge := by
  have hpoint (T : Finset V) (hT : T.card=t) (A : Finset V) (hA : A⊆T) (xi : Ξ)
      (hel : eligible T A xi) :
      (fixedSizeLaw (univ\T) (N-t)).prob (fun R =>
        ((G.interedges ((T∪R)∩S T A xi) ((T∪R)\S T A xi)).card:ℝ) ≤
          fraction T A xi*(M T A xi*(p:ℝ)^2)) ≤
        if ((S T A xi).card:ℝ) ≤ cutoff then etaSmall else etaLarge := by
    have hcard : (univ\T).card=Fintype.card V-t := by
      rw [card_sdiff_of_subset (subset_univ T),card_univ,hT]
    exact fixed_remaining_cut_label_tail G (S T A xi) T p (by rw [hcard]; omega)
      (by rwa [hcard]) hp hp0 (hvalid T hT A hA xi hel)
  apply fixed_marked_two_label_regimes_capped (univ:Finset V) (by simpa using hN) ht kap
    (fun U T xi A => eligible T A xi ∧ ((S T A xi).card:ℝ) ≤ cutoff ∧
      ((G.interedges (U∩S T A xi) (U\S T A xi)).card:ℝ) ≤ fraction T A xi*(M T A xi*(p:ℝ)^2))
    (fun U T xi A => eligible T A xi ∧ cutoff < ((S T A xi).card:ℝ) ∧
      ((G.interedges (U∩S T A xi) (U\S T A xi)).card:ℝ) ≤ fraction T A xi*(M T A xi*(p:ℝ)^2))
    hr heS
  · intro T _ hT xi A hA _
    by_cases hel : eligible T A xi
    · by_cases hs : ((S T A xi).card:ℝ) ≤ cutoff
      · have hb := hpoint T hT A hA xi hel
        rw [if_pos hs] at hb
        exact (FiniteLaw.prob_mono _ (fun _ h => h.2.2)).trans hb
      · simpa only [hs,false_and,and_false,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heS
    · simpa only [hel,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heS
  · intro T _ hT xi A hA
    by_cases hel : eligible T A xi
    · by_cases hs : cutoff < ((S T A xi).card:ℝ)
      · have hb := hpoint T hT A hA xi hel
        rw [if_neg (not_le.mpr hs)] at hb
        exact (FiniteLaw.prob_mono _ (fun _ h => h.2.2)).trans hb
      · simpa only [hs,false_and,and_false,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heL
    · simpa only [hel,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heL


theorem fixed_global_split_witness_upper_capped (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta tau q theta ell err nu rho cutoff etaSmall etaLarge : ℝ}
    (hz : 0 < z) (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm)
    (htheta : 0 < theta) (hscale : 0 < ell/theta) (hnu : 0 < nu)
    (hr : 0 < rho) (heS : 0 ≤ etaSmall) (heL : 0 ≤ etaLarge)
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
        (exp ((t:ℝ)*cappedLabelEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge) := by
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
      exp ((t:ℝ)*cappedLabelEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge := by
    exact fixed_marked_split_cut_bound_capped G hN ht (fixedMajorityLaw G) fixedMajoritySmallSide
      lambda M fraction eligible p hp0 hp hmean hr heS heL
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


theorem fixed_global_split_expansion_failure_bound_capped (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta tau q theta ell err nu rho cutoff etaSmall etaLarge : ℝ}
    (hz : 0 < z) (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm)
    (htheta : 0 < theta) (hscale : 0 < ell/theta) (hnu : 0 < nu)
    (hr : 0 < rho) (heS : 0 ≤ etaSmall) (heL : 0 ≤ etaLarge)
    (hnuBound : nu ≤
      (max (dm-tau) ((1-(tau-beta)/(tau+(dm-beta)/2))*(dm-beta))*z-err)/(ell/theta))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (hlabelBudget : (exp 1-1)*((t:ℝ)/N)*
      (((ell/theta)*cutoff+err)/(1-(tau-beta)/(tau+(dm-beta)/2)))+q ≤ rho*t)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    {voteLambda K omega : ℝ} (hdelta : 2 < dm*z) (hvotelambda : 3 ≤ voteLambda)
    (hvotemean : voteLambda ≤ ((t:ℝ)/N)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1+tau/dm-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1+tau/dm-rho)*(min 1 (poissonTailTwo voteLambda)+
        (1-min 1 (poissonTailTwo voteLambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (homega : 0 < omega)
    (hwitness : omega ≤ 1-(2*K*beta+(dm+tau)*exp (-voteLambda))/(tau-beta)-exp (-q))
    (lambda M fraction : Finset V → Finset V → (V → Finset V) → ℝ)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T p
        (lambda T A xi) (M T A xi) (fraction T A xi)
        (if ((fixedMajoritySmallSide T A xi).card:ℝ) ≤ cutoff then etaSmall else etaLarge) ∧
      tau*z*((ell/theta)*(fixedMajoritySmallSide T A xi).card+err) ≤
        fraction T A xi*(M T A xi*(p:ℝ)^2)) :
    (fixedSizeLaw (univ:Finset V) N).prob (FixedExpansionFailure G univ N z dm beta) ≤
      (2*exp (-theta*err)*(1+exp (theta-ell))^t+
        (exp ((t:ℝ)*cappedLabelEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge))/omega := by
  have hlower := fixed_majority_strong_bad_cut_transfer G (univ:Finset V) ht hz
    (hb.trans hbd) hb hbt hbd hdelta hvotelambda hvotemean hK hpure hmixed homega.le hwitness
  have hupper := fixed_global_split_witness_upper_capped G hN ht htD (q:=q) hz hb hbt hbd htheta hscale hnu
    hr heS heL hnuBound hmgf hlabelBudget p hp0 hp hmean lambda M fraction hvalid
  apply (le_div_iff₀ homega).mpr
  simpa only [mul_comm] using hlower.trans hupper


end
end Cycle12
