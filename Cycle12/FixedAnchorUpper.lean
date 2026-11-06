import Cycle12.FixedAnchorTransfer
import Cycle12.AnchorPopulationSharp
import Cycle12.FixedGlobalWitnessUpper
import Cycle12.FixedCutLabelTail

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_anchor_witness_upper (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta L ew miss theta ell intercept raw pLower ce nu tail : ℝ}
    (hz : 0 < z) (hdm : 0 < dm) (hb : 0 < beta) (hL : 0 < L) (hew : 0 ≤ ew)
    (hmiss1 : miss < 1) (htheta : 0 < theta) (hscale : 0 < ell/theta) (hce : 0 < ce)
    (hceFirst : ce ≤ 1-miss)
    (hceSecond : ce*min (1-pLower) ((1-raw)/(1-miss)) ≤ raw)
    (hNlower : pLower*Fintype.card V ≤ (N:ℝ))
    (hpop : (ell/theta)*(raw*Fintype.card V)+intercept ≤
      (N:ℝ)/2-(ew+2)*L*Fintype.card V/(dm*z))
    (hnu : nu ≤ max (min ((1-miss)*((beta*z)*(dm*z-L)/L)) (raw*Fintype.card V))
      ((dm*z-L-intercept)/((ell/theta)+(ew+2)*L/((dm*z)*ce))))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ)) (htail : 0 ≤ tail)
    (lambda M fraction : Finset V → Finset V → (V → Finset V) → ℝ)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T p
        (lambda T A xi) (M T A xi) (fraction T A xi) tail ∧
      ((1+ew)*L/ce)*(fixedMajoritySmallSide T A xi).card ≤
        fraction T A xi*(M T A xi*(p:ℝ)^2)) :
    (fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)).prob (fun x =>
      FixedAnchorMajorityWitness G N z dm beta L ew miss x.1 x.2.1 x.2.2) ≤
      2*exp (-theta*intercept)*(1+exp (theta-ell))^t+(2:ℝ)^t*tail := by
  let mu := fixedMarkedExperiment (univ:Finset V) N t (fixedMajorityLaw G)
  let eligible := fun (T A : Finset V) (xi : V → Finset V) =>
    nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ)
  let Ecount := fun x : Finset V×(Finset V×(V → Finset V)) =>
    fixedMajorityCountingFailure x.1 x.2.1 x.2.2 (ell/theta) intercept
  let Ecut := fun x : Finset V×(Finset V×(V → Finset V)) => ∃ A⊆x.2.1,
    eligible x.2.1 A x.2.2 ∧
      ((G.interedges (x.1∩fixedMajoritySmallSide x.2.1 A x.2.2)
        (x.1\fixedMajoritySmallSide x.2.1 A x.2.2)).card:ℝ) ≤
          fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2)
  have hcount : mu.prob Ecount ≤ 2*exp (-theta*intercept)*(1+exp (theta-ell))^t := by
    simpa only [mu,Ecount,fixedMajorityCountingFailure,card_univ] using
      fixed_majority_two_colors_counting_failure G (univ:Finset V)
        (by simpa using hN) ht (by simpa using htD) htheta (by simpa using hmgf) (err:=intercept)
  have hcut : mu.prob Ecut ≤ (2:ℝ)^t*tail :=
    fixed_marked_truncated_cut_bound G hN ht (fixedMajorityLaw G) fixedMajoritySmallSide
      lambda M fraction eligible p hp0 hp hmean htail
      (fun T hT A hA xi hel => (hvalid T hT A hA xi hel).1)
  have hincl : mu.prob (fun x =>
      FixedAnchorMajorityWitness G N z dm beta L ew miss x.1 x.2.1 x.2.2) ≤
      mu.prob (fun x => Ecount x ∨ Ecut x) := by
    apply FiniteLaw.prob_mono_support
    intro x hx hw
    by_cases hc : Ecount x
    · exact Or.inl hc
    have hs := fixed_marked_experiment_support (univ:Finset V) (by simpa using hN) ht
      (fixedMajorityLaw G) x hx
    have hgood := fixed_majority_not_counting_failure x.1 x.2.1 x.2.2 hc
    obtain ⟨hcard,hdeg,hexp,X,C,hbad,herror,hmiss⟩ := hw
    let S := fixedMajoritySide univ x.2.1 (C∩x.2.1) x.2.2
    have hg := anchor_oriented_sharp_population G x.1 X C S (mul_pos hdm hz) (mul_pos hb hz)
      hL hew hmiss1 hscale hce hceFirst hceSecond (by simpa only [hcard] using hNlower)
      (by simpa only [hcard] using hpop) hdeg hexp hbad herror hmiss
      (hgood (C∩x.2.1) inter_subset_right)
    have hel : eligible x.2.1 (C∩x.2.1) x.2.2 := hnu.trans hg.2.1
    have hX : (X.card:ℝ) ≤ ((smallerCutSide S).card:ℝ)/ce := by
      apply (le_div_iff₀ hce).mpr
      nlinarith only [hg.1]
    have hbudget := mul_le_mul_of_nonneg_left hX
      (mul_nonneg (show 0 ≤ 1+ew by linarith only [hew]) hL.le)
    have hactual : ((G.interedges (x.1∩smallerCutSide S) (x.1\smallerCutSide S)).card:ℝ) ≤
        ((1+ew)*L/ce)*(smallerCutSide S).card := by
      calc
        _ ≤ (1+ew)*L*X.card := hg.2.2
        _ ≤ (1+ew)*L*(((smallerCutSide S).card:ℝ)/ce) := hbudget
        _ = _ := by ring
    exact Or.inr ⟨C∩x.2.1,inter_subset_right,hel,
      hactual.trans (hvalid x.2.1 hs.2.2.2.1 (C∩x.2.1) inter_subset_right x.2.2 hel).2⟩
  exact hincl.trans ((mu.prob_union_le Ecount Ecut).trans (add_le_add hcount hcut))

end
end Cycle12
