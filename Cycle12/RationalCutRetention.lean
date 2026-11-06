import Cycle12.CoverFullProfileRetention

namespace Cycle12
open Finset SimpleGraph Cycle13

def ratClampedRetention (nu lambda alpha : ℚ) : ℚ :=
  let y := min nu (max 0 ((alpha-(lambda-1)*nu)/2))
  alpha-((alpha-(lambda-1)*nu)*y-y^2)/nu
def ratProfileQuadratic (nu lambda a t : ℚ) : ℚ := nu*(1-t)*(lambda-t)+a*t
def ratProfileMinimizer (nu lambda a lo hi : ℚ) : ℚ :=
  min hi (max lo ((nu*(lambda+1)-a)/(2*nu)))

theorem rat_clamped_retention_cast (nu lambda alpha : ℚ) :
    (ratClampedRetention nu lambda alpha:ℝ)=clampedRetention nu lambda alpha := by
  simp only [ratClampedRetention,clampedRetention,clampedHeavy,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_add,Rat.cast_min,Rat.cast_max,Rat.cast_div,Rat.cast_pow,Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat]
theorem rat_profile_quadratic_cast (nu lambda a t : ℚ) :
    (ratProfileQuadratic nu lambda a t:ℝ)=profileQuadratic nu lambda a t := by
  simp only [ratProfileQuadratic,profileQuadratic,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_one]
theorem rat_profile_minimizer_cast (nu lambda a lo hi : ℚ) :
    (ratProfileMinimizer nu lambda a lo hi:ℝ)=profileIntervalMinimizer nu lambda a lo hi := by
  simp only [ratProfileMinimizer,profileIntervalMinimizer,Rat.cast_min,Rat.cast_max,Rat.cast_sub,
    Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]

structure RatCutRetentionCertificate where
  xl : ℚ
  xh : ℚ
  ymax : ℚ
  nu : ℚ
  lambda : ℚ
  retained : ℚ
  useFine : Bool
  coarse : RatCutProfile
  fine : Fin 16 → RatCutProfile

def RatCutRetentionCertificate.ProfilesValid (c : RatCutRetentionCertificate) : Prop :=
  if c.useFine then ∀ i, (c.fine i).Valid else c.coarse.Valid

def RatCutRetentionCertificate.NumericValid (c : RatCutRetentionCertificate) : Prop :=
  c.xh ≤ 17/250 ∧ 0 < c.ymax ∧ c.ymax ≤ 1/2 ∧ 0 < c.nu ∧ 1 ≤ c.lambda ∧
  (if c.useFine then ∀ i : Fin 16,
    (c.fine i).xl=c.xl ∧ (c.fine i).xh=c.xh ∧
    ((i.val+1:ℚ)/16)*c.ymax ≤ (c.fine i).side ∧
    c.retained ≤ ratProfileQuadratic c.nu c.lambda (max 1 (c.fine i).alpha)
      (ratProfileMinimizer c.nu c.lambda (max 1 (c.fine i).alpha) ((i.val:ℚ)/16) ((i.val+1:ℚ)/16))
  else c.coarse.xl=c.xl ∧ c.coarse.xh=c.xh ∧ c.ymax ≤ c.coarse.side ∧
    c.retained ≤ ratClampedRetention c.nu c.lambda (max 1 c.coarse.alpha))

instance instDecidableRatRetentionProfiles (c : RatCutRetentionCertificate) : Decidable c.ProfilesValid := by
  unfold RatCutRetentionCertificate.ProfilesValid
  infer_instance
instance instDecidableRatRetentionNumeric (c : RatCutRetentionCertificate) : Decidable c.NumericValid := by
  unfold RatCutRetentionCertificate.NumericValid
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

def RatCutRetentionCertificate.Sound (c : RatCutRetentionCertificate) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    (0:ℝ) < Fintype.card V → (0:ℝ) < Fintype.card G.edgeSet → CoverSparseCutIrreducible G →
    (c.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) →
    coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (c.xh:ℝ) →
    0 < coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet) →
    (c.nu:ℝ)*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet) ≤ (S.card:ℝ) →
    (S.card:ℝ) ≤ (c.ymax:ℝ)*Fintype.card V →
    (c.retained:ℝ)*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card ≤
      (Fintype.card (truncatedCut G S (roundedCutCap c.lambda S)).edgeSet:ℝ)

theorem rat_cut_retention_certificate_sound (c : RatCutRetentionCertificate)
    (hp : c.ProfilesValid) (hc : c.NumericValid) : c.Sound := by
  obtain ⟨hmax,hym,hyhalf,hnu,hl,hbranch⟩ := hc
  have hmaxR : (c.xh:ℝ) ≤ 17/250 := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hmax
    norm_num at hh ⊢
    exact hh
  have hhalfR : (c.ymax:ℝ) ≤ 1/2 := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hyhalf
    norm_num at hh ⊢
    exact hh
  have hnR : (0:ℝ) < (c.nu:ℝ) := by exact_mod_cast hnu
  have hlR : (1:ℝ) ≤ (c.lambda:ℝ) := by exact_mod_cast hl
  intro V _ _ G S hn hm hI hxl hxh hh hside hupper
  have hhalf : 2*(S.card:ℝ) ≤ Fintype.card V := by
    have hb := mul_le_mul_of_nonneg_right hhalfR hn.le
    linarith only [hupper,hb]
  cases he : c.useFine with
  | false =>
    simp only [he,Bool.false_eq_true,if_false] at hbranch
    simp only [RatCutRetentionCertificate.ProfilesValid,he,Bool.false_eq_true,if_false] at hp
    obtain ⟨hcx,hch,hcs,hretain⟩ := hbranch
    have hbefore := truncated_cut_clamped_retained G S (roundedCutCap c.lambda S) hh hnR hlR
      ((le_div_iff₀ hh).mpr hside) (roundedCutCap_lower c.lambda S)
      (fun X hXS => cover_rational_irreducible_cut_profile G c.coarse hp hn hm
        (by rwa [hcx]) (by rwa [hch]) hI X (by
          have hX : (X.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card hXS
          have hys : (c.ymax:ℝ) ≤ (c.coarse.side:ℝ) := by exact_mod_cast hcs
          exact hX.trans (hupper.trans (mul_le_mul_of_nonneg_right hys hn.le))))
    have hk : (c.retained:ℝ) ≤ clampedRetention (c.nu:ℝ) (c.lambda:ℝ) (max 1 (c.coarse.alpha:ℝ)) := by
      simpa only [rat_clamped_retention_cast,Rat.cast_max,Rat.cast_one] using (Rat.cast_le (K:=ℝ)).mpr hretain
    have hb := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hh.le)
      (Nat.cast_nonneg (α:=ℝ) S.card)).trans hbefore
    simpa only [Set.fintypeCard_eq_ncard] using hb
  | true =>
    simp only [he,if_true] at hbranch
    simp only [RatCutRetentionCertificate.ProfilesValid,he,if_true] at hp
    apply cover_rational_full_profile_retained G S c.fine hp hn hm (hxh.trans hmaxR) hI
      (fun i => by rwa [(hbranch i).1]) (fun i => by rwa [(hbranch i).2.1])
      hh hnR hlR hside hupper hhalf
    · intro i
      have hb := (Rat.cast_le (K:=ℝ)).mpr (hbranch i).2.2.1
      simpa only [profileSixteenUpper,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,
        Rat.cast_one,Rat.cast_ofNat] using hb
    · intro i
      have hb := (Rat.cast_le (K:=ℝ)).mpr (hbranch i).2.2.2
      simpa only [rat_profile_quadratic_cast,rat_profile_minimizer_cast,profileSixteenLower,
        profileSixteenUpper,Rat.cast_max,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,
        Rat.cast_one,Rat.cast_ofNat] using hb

end
end Cycle12
