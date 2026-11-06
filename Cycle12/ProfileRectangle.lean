import Cycle12.ProfileIntervalMinimum

namespace Cycle12
open Finset Set SimpleGraph Cycle13
noncomputable section

/-- The original argument t*nu/R lies below both rectangle bounds.
Antitonicity therefore permits the smaller of these two upper bounds. -/
theorem profile_rectangle_lower (alpha : ℝ → ℝ)
    (halpha : AntitoneOn alpha (Set.Icc 0 (1/2)))
    {nu nuHi R Rlo t tHi a : ℝ}
    (hnu0 : 0 ≤ nu) (hnu : nu ≤ nuHi) (hRlo : 0<Rlo) (hR : Rlo ≤ R)
    (ht0 : 0 ≤ t) (ht : t ≤ tHi) (htHi : tHi ≤ 1) (hside : nu/R ≤ 1/2)
    (ha : a ≤ alpha (min (tHi*nuHi/Rlo) (tHi/2))) : a ≤ alpha (t*nu/R) := by
  have hRp := hRlo.trans_le hR
  have hthi : 0 ≤ tHi := ht0.trans ht
  have hnuHi : 0 ≤ nuHi := hnu0.trans hnu
  have hx0 : 0 ≤ t*nu/R := div_nonneg (mul_nonneg ht0 hnu0) hRp.le
  have h₁ : t*nu/R ≤ tHi*nuHi/Rlo := by
    exact (div_le_div_of_nonneg_right (mul_le_mul ht hnu hnu0 hthi) hRp.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hthi hnuHi) hRlo hR)
  have h₂ : t*nu/R ≤ tHi/2 := by
    have hh := mul_le_mul_of_nonneg_left hside ht0
    calc
      t*nu/R=t*(nu/R) := by ring
      _ ≤ t/2 := by simpa only [mul_one_div] using hh
      _ ≤ tHi/2 := div_le_div_of_nonneg_right ht (by norm_num)
  have hy0 : 0 ≤ min (tHi*nuHi/Rlo) (tHi/2) := by positivity
  have hy1 : min (tHi*nuHi/Rlo) (tHi/2) ≤ 1/2 :=
    (min_le_right _ _).trans (by linarith)
  have hxy := le_min h₁ h₂
  exact ha.trans (halpha ⟨hx0,hxy.trans hy1⟩ ⟨hy0,hy1⟩ hxy)

theorem profile_quantized_lower (alpha : ℝ → ℝ)
    (halpha : AntitoneOn alpha (Set.Icc 0 (1/2))) {y rounded a : ℝ}
    (hy : 0 ≤ y) (hround : y ≤ rounded) (hhalf : rounded ≤ 1/2)
    (ha : a ≤ alpha rounded) : a ≤ alpha y :=
  ha.trans (halpha ⟨hy,hround.trans hhalf⟩ ⟨hy.trans hround,hhalf⟩ hround)

def profileSixteenLower (i : Fin 16) : ℝ := i.val/16
def profileSixteenUpper (i : Fin 16) : ℝ := (i.val+1)/16

theorem profile_sixteen_cover (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ i : Fin 16, profileSixteenLower i ≤ t ∧ t ≤ profileSixteenUpper i := by
  by_cases h1 : t ≤ 1/16
  · exact ⟨0,by simpa [profileSixteenLower] using ht0,by convert h1 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h2 : t ≤ 2/16
  · exact ⟨1,by simpa [profileSixteenLower] using (le_of_not_ge h1),by convert h2 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h3 : t ≤ 3/16
  · exact ⟨2,by simpa [profileSixteenLower] using (le_of_not_ge h2),by convert h3 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h4 : t ≤ 4/16
  · exact ⟨3,by simpa [profileSixteenLower] using (le_of_not_ge h3),by convert h4 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h5 : t ≤ 5/16
  · exact ⟨4,by simpa [profileSixteenLower] using (le_of_not_ge h4),by convert h5 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h6 : t ≤ 6/16
  · exact ⟨5,by simpa [profileSixteenLower] using (le_of_not_ge h5),by convert h6 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h7 : t ≤ 7/16
  · exact ⟨6,by simpa [profileSixteenLower] using (le_of_not_ge h6),by convert h7 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h8 : t ≤ 8/16
  · exact ⟨7,by simpa [profileSixteenLower] using (le_of_not_ge h7),by convert h8 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h9 : t ≤ 9/16
  · exact ⟨8,by simpa [profileSixteenLower] using (le_of_not_ge h8),by convert h9 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h10 : t ≤ 10/16
  · exact ⟨9,by simpa [profileSixteenLower] using (le_of_not_ge h9),by convert h10 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h11 : t ≤ 11/16
  · exact ⟨10,by simpa [profileSixteenLower] using (le_of_not_ge h10),by convert h11 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h12 : t ≤ 12/16
  · exact ⟨11,by simpa [profileSixteenLower] using (le_of_not_ge h11),by convert h12 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h13 : t ≤ 13/16
  · exact ⟨12,by simpa [profileSixteenLower] using (le_of_not_ge h12),by convert h13 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h14 : t ≤ 14/16
  · exact ⟨13,by simpa [profileSixteenLower] using (le_of_not_ge h13),by convert h14 using 1 <;> norm_num [profileSixteenUpper]⟩
  by_cases h15 : t ≤ 15/16
  · exact ⟨14,by simpa [profileSixteenLower] using (le_of_not_ge h14),by convert h15 using 1 <;> norm_num [profileSixteenUpper]⟩
  · exact ⟨15,by simpa [profileSixteenLower] using (le_of_not_ge h15),by convert ht1 using 1 <;> norm_num [profileSixteenUpper]⟩

attribute [local instance] Classical.propDecidable

/-- Instantiate a checked full-profile interval table on an actual
truncated cut. The conclusion counts retained graph edges. -/
theorem truncated_cut_profile_table {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) (k : ℕ) (alpha : ℝ → ℝ)
    (lo hi lower : I → ℝ) {h N lambda nuLower kappa : ℝ}
    (hh : 0<h) (hN : 0<N) (hS : S.Nonempty) (hlambda : 1 ≤ lambda)
    (hn : 0<nuLower) (hnu : nuLower ≤ S.card/h) (hcap : lambda*S.card ≤ (k:ℝ))
    (hprofile : ∀ X⊆S, alpha ((X.card:ℝ)/N)*h*X.card ≤ (cutSize G X:ℝ))
    (hcover : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ i, lo i ≤ t ∧ t ≤ hi i)
    (hlower : ∀ i t, 0 ≤ t → t ≤ 1 → lo i ≤ t → t ≤ hi i →
      lower i ≤ alpha (t*(S.card/h)/(N/h)))
    (hcheck : ∀ i, kappa ≤ profileQuadratic nuLower lambda (lower i)
      (profileIntervalMinimizer nuLower lambda (lower i) (lo i) (hi i))) :
    kappa*h*S.card ≤ ((truncatedCut G S k).edgeSet.ncard:ℝ) := by
  obtain ⟨t,ht0,ht1,ht⟩ := truncated_cut_full_profile_scaled G S k alpha hh hN hS hcap hprofile
  have hbound := profile_finite_interval_bound lo hi lower alpha hn hnu hlambda
    hcover hlower hcheck ht0 ht1
  have hs : (0:ℝ)<S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hb := (le_div_iff₀ (mul_pos hh hs)).mp (hbound.trans ht)
  nlinarith only [hb]

end
end Cycle12
