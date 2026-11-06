import Cycle12.RestrictedPopulation
import Cycle12.FixedReverseCounting
import Cycle12.FixedBinnedCutTail
import Cycle12.FixedGlobalWitnessUpper

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]

/-- Actual restricted witnesses are covered by forward counting, reverse
counting and the finite family of truncated-cut tails. In particular the
classified side is not replaced by a globally minimizing cut. -/
theorem fixed_restricted_witness_upper (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta err eta q theta ell intercept nu size reverseMean reverseFraction : ℝ}
    (hz : 0 < z) (hbe : 0 ≤ beta+err) (hc : (err+2*beta)/dm < 1)
    (htheta : 0 < theta) (hscale : 0 < ell/theta)
    (hnuBound : nu ≤ (((1-(err+2*beta)/dm)*(dm-beta))*z-intercept)/(ell/theta))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (hrMean : 0 < reverseMean) (hr0 : 0 < reverseFraction) (hr1 : reverseFraction < 1)
    (hrmean : reverseMean ≤ (((N-t:ℕ):ℝ)/(Fintype.card V-t:ℕ))*(size-t))
    (hlocal : (1+(err+2*beta)/dm)*eta*N < reverseFraction*reverseMean)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    (lambda M fraction : I → Finset V → Finset V → (V → Finset V) → ℝ)
    (eligible : I → Finset V → Finset V → (V → Finset V) → Prop)
    (rho tail : I → ℝ) (hrho : ∀ i, 0 < rho i) (htail : ∀ i, 0 ≤ tail i)
    (hcover : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySide univ T A xi).card:ℝ) →
      ((fixedMajoritySide univ T A xi).card:ℝ) < size → ∃ i, eligible i T A xi)
    (hvalid : ∀ i T, T.card=t → ∀ A⊆T, ∀ xi, eligible i T A xi →
      RoundedCutLabelValid G (fixedMajoritySide univ T A xi) T p
        (lambda i T A xi) (M i T A xi) (fraction i T A xi) (tail i) ∧
      (beta+err)*z*(((ell/theta)*(fixedMajoritySide univ T A xi).card+intercept)/
        (1-(err+2*beta)/dm)) ≤ fraction i T A xi*(M i T A xi*(p:ℝ)^2) ∧
      (exp 1-1)*((t:ℝ)/N)*
        (((ell/theta)*(fixedMajoritySide univ T A xi).card+intercept)/(1-(err+2*beta)/dm))+q ≤ rho i*t) :
    (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob (fun x =>
      FixedRestrictedMajorityWitness G univ x.1 x.2.1 x.2.2 t z dm beta err eta q) ≤
      2*exp (-theta*intercept)*(1+exp (theta-ell))^t+
        (2:ℝ)^t*exp (-(1-reverseFraction)^2*reverseMean/2)+
        ∑ i, exp ((t:ℝ)*cappedLabelEntropy (rho i))*tail i := by
  let mu := fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)
  let Ecount := fun x : Finset V×(Finset V×(V → Finset V)) =>
    fixedMajorityCountingFailure x.1 x.2.1 x.2.2 (ell/theta) intercept
  let Ereverse := fun x : Finset V×(Finset V×(V → Finset V)) => ∃ A⊆x.2.1,
    size ≤ ((fixedMajoritySide univ x.2.1 A x.2.2).card:ℝ) ∧
      ((x.1∩fixedMajoritySide univ x.2.1 A x.2.2).card:ℝ) < reverseFraction*reverseMean
  let Ecut := fun x : Finset V×(Finset V×(V → Finset V)) => ∃ i, ∃ A⊆x.2.1,
    (A.card:ℝ) ≤ rho i*t ∧ eligible i x.2.1 A x.2.2 ∧
      ((G.interedges (x.1∩fixedMajoritySide univ x.2.1 A x.2.2)
        (x.1\fixedMajoritySide univ x.2.1 A x.2.2)).card:ℝ) ≤
          fraction i x.2.1 A x.2.2*(M i x.2.1 A x.2.2*(p:ℝ)^2)
  have hcount : mu.prob Ecount ≤ 2*exp (-theta*intercept)*(1+exp (theta-ell))^t := by
    simpa only [mu,Ecount,fixedMajorityCountingFailure,card_univ] using
      fixed_majority_two_colors_counting_failure G (univ:Finset V)
        (by simpa using hN) ht (by simpa using htD) htheta (by simpa using hmgf) (err:=intercept)
  have hreverse : mu.prob Ereverse ≤ (2:ℝ)^t*exp (-(1-reverseFraction)^2*reverseMean/2) :=
    fixed_marked_reverse_count_bound hN ht htD (fixedMajorityLaw G) (fixedMajoritySide univ)
      hrMean hr0 hr1 hrmean
  have hcut : mu.prob Ecut ≤ ∑ i, exp ((t:ℝ)*cappedLabelEntropy (rho i))*tail i :=
    fixed_marked_binned_cut_bound G hN ht (fixedMajorityLaw G) (fixedMajoritySide univ)
      lambda M fraction eligible p hp0 hp hmean rho tail hrho htail
      (fun i T hT A hA xi hel => (hvalid i T hT A hA xi hel).1)
  have hincl : mu.prob (fun x =>
      FixedRestrictedMajorityWitness G univ x.1 x.2.1 x.2.2 t z dm beta err eta q) ≤
      mu.prob (fun x => (Ecount x ∨ Ereverse x) ∨ Ecut x) := by
    apply FiniteLaw.prob_mono_support
    intro x hx hw
    by_cases hc' : Ecount x
    · exact Or.inl (Or.inl hc')
    by_cases hr' : Ereverse x
    · exact Or.inl (Or.inr hr')
    have hs := fixed_marked_experiment_support (univ:Finset V) (by simpa using hN) ht
      (fixedMajorityLaw G) x hx
    have hgood := fixed_majority_not_counting_failure x.1 x.2.1 x.2.2 hc'
    have hrev : ∀ A⊆x.2.1, size ≤ ((fixedMajoritySide univ x.2.1 A x.2.2).card:ℝ) →
        reverseFraction*reverseMean ≤ ((x.1∩fixedMajoritySide univ x.2.1 A x.2.2).card:ℝ) := by
      intro A hA hsize
      exact le_of_not_gt (fun h => hr' ⟨A,hA,hsize,h⟩)
    obtain ⟨A,hA,hpop,hsize,hsmall,hlabel⟩ := restricted_majority_localizes G x.1 x.2.1
      x.2.2 hs.2.1 hz hbe hscale hc hlocal hw (fun A hA => (hgood A hA).1) hrev
    obtain ⟨i,hel⟩ := hcover x.2.1 hs.2.2.2.1 A hA x.2.2 (hnuBound.trans hpop) hsize
    have hv := hvalid i x.2.1 hs.2.2.2.1 A hA x.2.2 hel
    exact Or.inr ⟨i,A,hA,hlabel.trans hv.2.2,hel,hsmall.trans hv.2.1⟩
  exact hincl.trans ((mu.prob_union_le (fun x => Ecount x ∨ Ereverse x) Ecut).trans
    (add_le_add ((mu.prob_union_le Ecount Ereverse).trans (add_le_add hcount hreverse)) hcut))

end
end Cycle12
