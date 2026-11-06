import Cycle12.MajorityPopulation

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The minority label restriction is charged only on the selected small
population regime. The large regime retains the unrestricted label set. -/
theorem strong_majority_split_witness (G : SimpleGraph V) (U T : Finset V)
    (xi : V → Finset V) {N t : ℕ} (hcard : U.card=N)
    {z dm beta tau q scale err cutoff rho : ℝ}
    (hz : 0 < z) (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm) (hscale : 0 < scale)
    (hw : FixedGlobalStrongMajorityWitness G univ U T xi t z dm beta tau q)
    (hgood : ∀ A⊆T,
      ((U∩fixedMajoritySide univ T A xi).card:ℝ) ≤ scale*(fixedMajoritySide univ T A xi).card+err ∧
      ((U\fixedMajoritySide univ T A xi).card:ℝ) ≤ scale*(fixedMajoritySide univ T A xi)ᶜ.card+err)
    (hlabelBudget : (exp 1-1)*((t:ℝ)/N)*
      ((scale*cutoff+err)/(1-(tau-beta)/(tau+(dm-beta)/2)))+q ≤ rho*t) :
    ∃ A⊆T,
      (max (dm-tau) ((1-(tau-beta)/(tau+(dm-beta)/2))*(dm-beta))*z-err)/scale ≤
        ((fixedMajoritySmallSide T A xi).card:ℝ) ∧
      ((G.interedges (U∩fixedMajoritySmallSide T A xi) (U\fixedMajoritySmallSide T A xi)).card:ℝ) ≤
        tau*z*(scale*(fixedMajoritySmallSide T A xi).card+err) ∧
      ((((fixedMajoritySmallSide T A xi).card:ℝ) ≤ cutoff ∧ (A.card:ℝ) ≤ rho*t) ∨
        cutoff < ((fixedMajoritySmallSide T A xi).card:ℝ)) := by
  obtain ⟨A,hA,hpop,hcut,hlabel⟩ := strong_majority_oriented_witness G U T xi hz hb hbt hbd hscale hw hgood
  refine ⟨A,hA,hpop,hcut,?_⟩
  by_cases hsmall : ((fixedMajoritySmallSide T A xi).card:ℝ) ≤ cutoff
  · apply Or.inl
    refine ⟨hsmall,?_⟩
    rw [hcard] at hlabel
    have hc := (joint_error_fraction_bounds hb hbt hbd).2
    have hscaled := mul_le_mul_of_nonneg_left hsmall hscale.le
    have hquot := div_le_div_of_nonneg_right (add_le_add hscaled (le_refl err)) (sub_nonneg.mpr hc.le)
    have hcoef : 0 ≤ (exp 1-1)*((t:ℝ)/N) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr (one_le_exp_iff.mpr (by norm_num))
      · positivity
    have hm := mul_le_mul_of_nonneg_left hquot hcoef
    exact hlabel.trans ((add_le_add hm le_rfl).trans hlabelBudget)
  · exact Or.inr (lt_of_not_ge hsmall)

end
end Cycle12
