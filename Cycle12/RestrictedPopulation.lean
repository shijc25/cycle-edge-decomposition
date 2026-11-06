import Cycle12.FixedRestrictedTransfer

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Localizing a restricted witness uses a separate reverse-count event.
No global minimizing-cut property is needed or asserted. -/
theorem restricted_majority_localizes (G : SimpleGraph V) (U T : Finset V)
    (xi : V → Finset V) {N t : ℕ} (hcard : U.card=N)
    {z dm beta err eta q scale intercept size reverseLower : ℝ}
    (hz : 0 < z) (hbetaerr : 0 ≤ beta+err) (hscale : 0 < scale)
    (hc : (err+2*beta)/dm < 1)
    (hlocal : (1+(err+2*beta)/dm)*eta*N < reverseLower)
    (hw : FixedRestrictedMajorityWitness G univ U T xi t z dm beta err eta q)
    (hgood : ∀ A⊆T,
      ((U∩fixedMajoritySide univ T A xi).card:ℝ) ≤ scale*(fixedMajoritySide univ T A xi).card+intercept)
    (hreverse : ∀ A⊆T, size ≤ ((fixedMajoritySide univ T A xi).card:ℝ) →
      reverseLower ≤ ((U∩fixedMajoritySide univ T A xi).card:ℝ)) :
    ∃ A⊆T,
      (((1-(err+2*beta)/dm)*(dm-beta))*z-intercept)/scale ≤
        ((fixedMajoritySide univ T A xi).card:ℝ) ∧
      ((fixedMajoritySide univ T A xi).card:ℝ) < size ∧
      ((G.interedges (U∩fixedMajoritySide univ T A xi) (U\fixedMajoritySide univ T A xi)).card:ℝ) ≤
        (beta+err)*z*((scale*(fixedMajoritySide univ T A xi).card+intercept)/(1-(err+2*beta)/dm)) ∧
      (A.card:ℝ) ≤ (exp 1-1)*((t:ℝ)/N)*
        ((scale*(fixedMajoritySide univ T A xi).card+intercept)/(1-(err+2*beta)/dm))+q := by
  obtain ⟨A,hAU,hAn,hsmall,hAsmall,ha,hB,hC,herror,hmin,hupper,hcut,hlabel⟩ := hw
  let S := fixedMajoritySide univ T (A∩T) xi
  let B := U∩S
  let c : ℝ := (err+2*beta)/dm
  have hcomp : U\B=U\S := by ext v; simp [B]
  change (1-c)*A.card ≤ min (B.card:ℝ) (U\B).card at hmin
  change (B.card:ℝ) ≤ (1+c)*A.card at hupper
  change ((G.interedges B (U\B)).card:ℝ) ≤ (beta+err)*z*A.card at hcut
  have hcount := hgood (A∩T) inter_subset_right
  change (B.card:ℝ) ≤ scale*S.card+intercept at hcount
  have hlow := hmin.trans (min_le_left _ _)
  have hcx0 : 0 ≤ c := by
    have ha0 : (0:ℝ) < A.card := by exact_mod_cast hAn.card_pos
    have hnon := Nat.cast_nonneg (α:=ℝ) (symmDiff A B).card
    change ((symmDiff A B).card:ℝ) ≤ c*A.card at herror
    nlinarith only [herror,hnon,ha0]
  have hloc : (S.card:ℝ) < size := by
    by_contra! hlarge
    have hrev := hreverse (A∩T) inter_subset_right hlarge
    have hmul := mul_le_mul_of_nonneg_left hAsmall (show 0 ≤ 1+c by linarith only [hcx0])
    rw [hcard] at hmul
    change reverseLower ≤ (B.card:ℝ) at hrev
    change (1+c)*eta*N < reverseLower at hlocal
    nlinarith only [hrev,hupper,hmul,hlocal]
  have haUpper : (A.card:ℝ) ≤ (scale*S.card+intercept)/(1-c) := by
    apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
    nlinarith only [hlow,hcount]
  refine ⟨A∩T,inter_subset_right,?_,hloc,?_,?_⟩
  · have hstrong := mul_lt_mul_of_pos_left ha (sub_pos.mpr hc)
    apply (div_le_iff₀ hscale).mpr
    change (1-c)*(dm-beta)*z-intercept ≤ (S.card:ℝ)*scale
    nlinarith only [hstrong,hlow,hcount]
  · have hm := mul_le_mul_of_nonneg_left haUpper (mul_nonneg hbetaerr hz.le)
    change ((G.interedges (U∩S) (U\S)).card:ℝ) ≤ _
    rw [hcomp] at hcut
    exact hcut.trans hm
  · have hlabel' : ((A∩T).card:ℝ) ≤ (exp 1-1)*((t:ℝ)/N)*A.card+q := by
      simpa only [hcard,inter_comm T A] using hlabel
    have he : 0 ≤ (exp 1-1)*((t:ℝ)/N) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr (one_le_exp_iff.mpr (by norm_num))
      · positivity
    exact hlabel'.trans (add_le_add (mul_le_mul_of_nonneg_left haUpper he) le_rfl)

end
end Cycle12
