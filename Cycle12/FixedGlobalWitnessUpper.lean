import Cycle12.MajorityPopulation
import Cycle12.FixedMarkedGraphJanson
import Cycle12.FixedMarkedSupport

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def fixedMajorityCountingFailure (U T : Finset V) (xi : V → Finset V) (scale err : ℝ) : Prop :=
  ∃ A⊆T,
    scale*(fixedMajoritySide univ T A xi).card+err < ((U∩fixedMajoritySide univ T A xi).card:ℝ) ∨
    scale*(univ\fixedMajoritySide univ T A xi).card+err <
      ((U∩(univ\fixedMajoritySide univ T A xi)).card:ℝ)

theorem fixed_majority_not_counting_failure (U T : Finset V) (xi : V → Finset V)
    {scale err : ℝ} (hgood : ¬fixedMajorityCountingFailure U T xi scale err) :
    ∀ A⊆T,
      ((U∩fixedMajoritySide univ T A xi).card:ℝ) ≤ scale*(fixedMajoritySide univ T A xi).card+err ∧
      ((U\fixedMajoritySide univ T A xi).card:ℝ) ≤ scale*(fixedMajoritySide univ T A xi)ᶜ.card+err := by
  intro A hA
  have h₁ : ¬scale*(fixedMajoritySide univ T A xi).card+err <
      ((U∩fixedMajoritySide univ T A xi).card:ℝ) := fun h => hgood ⟨A,hA,Or.inl h⟩
  have h₂ : ¬scale*(univ\fixedMajoritySide univ T A xi).card+err <
      ((U∩(univ\fixedMajoritySide univ T A xi)).card:ℝ) := fun h => hgood ⟨A,hA,Or.inr h⟩
  have hc : univ\fixedMajoritySide univ T A xi=(fixedMajoritySide univ T A xi)ᶜ := by ext v; simp
  have hi : U∩(univ\fixedMajoritySide univ T A xi)=U\fixedMajoritySide univ T A xi := by ext v; simp
  refine ⟨le_of_not_gt h₁,?_⟩
  have hh := le_of_not_gt h₂
  rw [hi,hc] at hh
  exact hh

/-- Closed upper bound for actual global stable-cut witnesses, using
fixed-size counting, the two truncated dependency bounds and Janson.
The remaining inputs are deterministic retention and numerical budgets. -/
theorem fixed_global_majority_witness_upper (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta tau q theta ell err nu eta : ℝ}
    (hz : 0 < z) (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm)
    (htheta : 0 < theta) (hscale : 0 < ell/theta) (hnu : 0 < nu) (heta : 0 ≤ eta)
    (hnuBound : nu ≤
      (max (dm-tau) ((1-(tau-beta)/(tau+(dm-beta)/2))*(dm-beta))*z-err)/(ell/theta))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    (lambda M fraction : Finset V → Finset V → (V → Finset V) → ℝ)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      1 ≤ lambda T A xi ∧ 0 < M T A xi ∧
      M T A xi ≤ (Fintype.card (truncatedResidualGraph G (fixedMajoritySmallSide T A xi) T
        (roundedCutCap (lambda T A xi) (fixedMajoritySmallSide T A xi))).edgeSet:ℝ) ∧
      0 ≤ fraction T A xi ∧ fraction T A xi ≤ 1 ∧
      tau*z*((ell/theta)*(fixedMajoritySmallSide T A xi).card+err) ≤
        fraction T A xi*(M T A xi*(p:ℝ)^2) ∧
      2*exp (-fullJansonPhi (fraction T A xi)*(M T A xi)*(p:ℝ)^2/
        (1+min ((lambda T A xi+1)*(fixedMajoritySmallSide T A xi).card)
          (lambda T A xi*(fixedMajoritySmallSide T A xi).card+1+
            M T A xi/(lambda T A xi*(fixedMajoritySmallSide T A xi).card))*(p:ℝ))) ≤ eta) :
    (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob (fun x =>
      FixedGlobalStrongMajorityWitness G univ x.1 x.2.1 x.2.2 t z dm beta tau q) ≤
        2*exp (-theta*err)*(1+exp (theta-ell))^t+(2:ℝ)^t*eta := by
  let eligible := fun (T A : Finset V) (xi : V → Finset V) =>
    nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ)
  let Ecount := fun x : Finset V×(Finset V×(V → Finset V)) =>
    fixedMajorityCountingFailure x.1 x.2.1 x.2.2 (ell/theta) err
  let Ecut := fun x : Finset V×(Finset V×(V → Finset V)) => ∃ A⊆x.2.1,
    eligible x.2.1 A x.2.2 ∧
      ((G.interedges (x.1∩fixedMajoritySmallSide x.2.1 A x.2.2)
        (x.1\fixedMajoritySmallSide x.2.1 A x.2.2)).card:ℝ) ≤
        fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2)
  have hcount : (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob Ecount ≤
      2*exp (-theta*err)*(1+exp (theta-ell))^t := by
    simpa only [Ecount,fixedMajorityCountingFailure,card_univ] using
      fixed_majority_two_colors_counting_failure G (univ:Finset V)
        (by simpa using hN) ht (by simpa using htD) htheta (by simpa using hmgf) (err:=err)
  have htail : (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob Ecut ≤
      (2:ℝ)^t*eta := by
    apply fixed_marked_truncated_cut_bound G hN ht (fixedMajorityLaw G) fixedMajoritySmallSide
      lambda M fraction eligible p hp0 hp hmean heta
    intro T hT A hA xi hel
    obtain ⟨hl,hM,hret,hf0,hf1,_,hbudget⟩ := hvalid T hT A hA xi hel
    have hS : (fixedMajoritySmallSide T A xi).Nonempty := by
      apply card_pos.mp
      exact_mod_cast hnu.trans_le hel
    exact ⟨hS,hl,hM,hret,hf0,hf1,hbudget⟩
  have hincl : (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob
      (fun x => FixedGlobalStrongMajorityWitness G univ x.1 x.2.1 x.2.2 t z dm beta tau q) ≤
      (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob (fun x => Ecount x ∨ Ecut x) := by
    apply FiniteLaw.prob_mono_support
    intro x hx hw
    by_cases hc : Ecount x
    · exact Or.inl hc
    · have hgood := fixed_majority_not_counting_failure x.1 x.2.1 x.2.2 hc
      obtain ⟨A,hA,hpop,hcut,_⟩ := strong_majority_oriented_witness G x.1 x.2.1 x.2.2
        hz hb hbt hbd hscale hw hgood
      have hel : eligible x.2.1 A x.2.2 := hnuBound.trans hpop
      have hs := fixed_marked_experiment_support (univ:Finset V) (by simpa using hN) ht
        (fixedMajorityLaw G) x hx
      have hbound := (hvalid x.2.1 hs.2.2.2.1 A hA x.2.2 hel).2.2.2.2.2.1
      exact Or.inr ⟨A,hA,hel,hcut.trans hbound⟩
  exact hincl.trans (((fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob_union_le
    Ecount Ecut).trans (add_le_add hcount htail))

end
end Cycle12
