import Cycle12.CoverPopulationBounds

namespace Cycle12
open Real Cycle13

structure RatPopulationCertificate where
  witness : RatWitnessCertificate
  Rlo : ℚ
  Wlo : ℚ
  pl : ℚ
  slope : ℚ
  intercept : ℚ
  cap : ℚ
  raw : ℚ
  ce : ℚ
  nu : ℚ

def RatPopulationCertificate.BranchValid (c : RatPopulationCertificate) : Prop :=
  match c.witness.kind with
  | .globalCut =>
    (c.witness.factor-c.witness.beta)/(c.witness.factor+(c.witness.dm-c.witness.beta)/2) ≤ c.cap ∧
    c.nu*c.slope ≤ max (c.witness.dm-c.witness.factor) ((1-c.cap)*(c.witness.dm-c.witness.beta))-c.intercept
  | .localCut =>
    (c.witness.error+2*c.witness.beta)/c.witness.dm ≤ c.cap ∧ c.cap < 1 ∧
    c.nu*c.slope ≤ (1-c.cap)*(c.witness.dm-c.witness.beta)-c.intercept
  | .anchor =>
    0 ≤ c.raw ∧ 0 < c.ce ∧ c.ce ≤ 7/8 ∧
    c.ce*min (1-c.pl) ((1-c.raw)/(1-1/8)) ≤ c.raw ∧
    0 ≤ c.witness.factor+2 ∧ c.witness.L/c.witness.zlo ≤ c.witness.dm ∧
    c.slope*c.raw+c.intercept/c.Rlo+(c.witness.factor+2)*c.witness.L/(c.witness.dm*c.Wlo) ≤ 1/2 ∧
    ((c.nu ≤ (7/8)*c.witness.beta*(c.witness.dm-c.witness.L/c.witness.zlo)*c.Wlo/c.witness.L ∧
        c.nu ≤ c.raw*c.Rlo) ∨
      c.nu*(c.slope+(c.witness.factor+2)*c.witness.L/(c.witness.dm*c.Wlo*c.ce)) ≤
        c.witness.dm-c.witness.L/c.witness.zlo-c.intercept)

def RatPopulationCertificate.Valid (c : RatPopulationCertificate) : Prop :=
  0 < c.Rlo ∧ 0 < c.Wlo ∧ 0 < c.slope ∧ 0 ≤ c.intercept ∧ 0 < c.nu ∧
  c.witness.beta ≤ c.witness.dm ∧ c.BranchValid

instance instDecidableRatPopulationBranchValid (c : RatPopulationCertificate) : Decidable c.BranchValid := by
  unfold RatPopulationCertificate.BranchValid
  cases c.witness.kind <;> infer_instance
instance instDecidableRatPopulationValid (c : RatPopulationCertificate) : Decidable c.Valid := by
  unfold RatPopulationCertificate.Valid
  infer_instance

noncomputable section

def RatPopulationCertificate.BranchBound (c : RatPopulationCertificate) (p z R : ℝ) : Prop :=
  match c.witness.kind with
  | .globalCut =>
    (c.nu:ℝ)*z/p ≤
      (max ((c.witness.dm:ℝ)-(c.witness.factor:ℝ))
        ((1-((c.witness.factor:ℝ)-(c.witness.beta:ℝ))/((c.witness.factor:ℝ)+((c.witness.dm:ℝ)-(c.witness.beta:ℝ))/2))*
          ((c.witness.dm:ℝ)-(c.witness.beta:ℝ)))*z-(c.intercept:ℝ)*z)/((c.slope:ℝ)*p)
  | .localCut =>
    (c.nu:ℝ)*z/p ≤ (((1-((c.witness.error:ℝ)+2*(c.witness.beta:ℝ))/(c.witness.dm:ℝ))*
      ((c.witness.dm:ℝ)-(c.witness.beta:ℝ)))*z-(c.intercept:ℝ)*z)/((c.slope:ℝ)*p)
  | .anchor =>
    (c.ce:ℝ) ≤ 1-1/8 ∧ (c.ce:ℝ)*min (1-(c.pl:ℝ)) ((1-(c.raw:ℝ))/(1-1/8)) ≤ (c.raw:ℝ) ∧
    ((c.slope:ℝ)*p)*((c.raw:ℝ)*(z*R/p))+(c.intercept:ℝ)*z ≤
      z*R/2-((c.witness.factor:ℝ)+2)*(c.witness.L:ℝ)*(z*R/p)/((c.witness.dm:ℝ)*z) ∧
    (c.nu:ℝ)*z/p ≤ max
      (min ((1-1/8)*(((c.witness.beta:ℝ)*z)*((c.witness.dm:ℝ)*z-(c.witness.L:ℝ))/(c.witness.L:ℝ)))
        ((c.raw:ℝ)*(z*R/p)))
      (((c.witness.dm:ℝ)*z-(c.witness.L:ℝ)-(c.intercept:ℝ)*z)/
        ((c.slope:ℝ)*p+((c.witness.factor:ℝ)+2)*(c.witness.L:ℝ)/(((c.witness.dm:ℝ)*z)*(c.ce:ℝ))))

def RatPopulationCertificate.Sound (c : RatPopulationCertificate) : Prop :=
  ∀ p z R : ℝ, 0 < p → (c.witness.zlo:ℝ) ≤ z → (c.Rlo:ℝ) ≤ R → (c.Wlo:ℝ) ≤ p*z →
    c.BranchBound p z R

theorem rat_population_certificate_sound (c : RatPopulationCertificate) (hc : c.Valid)
    (hw : c.witness.Valid) : c.Sound := by
  obtain ⟨hR,hW,hs,hitc,hnu,hbd,hbranch⟩ := hc
  obtain ⟨_,hdm,hb,hzlo,_,hL,_,_,_,_,_,_⟩ := hw
  have hR0 : (0:ℝ) < (c.Rlo:ℝ) := by exact_mod_cast hR
  have hW0 : (0:ℝ) < (c.Wlo:ℝ) := by exact_mod_cast hW
  have hs0 : (0:ℝ) < (c.slope:ℝ) := by exact_mod_cast hs
  have hdm0 : (0:ℝ) < (c.witness.dm:ℝ) := by exact_mod_cast hdm
  have hz0 : (0:ℝ) < (c.witness.zlo:ℝ) := by exact_mod_cast hzlo
  have hL0 : (0:ℝ) < (c.witness.L:ℝ) := by exact_mod_cast hL
  intro p z R hp hz hRl hWl
  cases hk : c.witness.kind with
  | globalCut =>
    rw [RatPopulationCertificate.BranchValid,hk] at hbranch
    obtain ⟨hcap,hnub⟩ := hbranch
    rw [RatPopulationCertificate.BranchBound,hk]
    apply global_population_lower_from_cap (cap:=(c.cap:ℝ)) hp (hz0.trans_le hz) hs0 (by exact_mod_cast hbd)
    · exact_mod_cast hcap
    · exact_mod_cast hnub
  | localCut =>
    rw [RatPopulationCertificate.BranchValid,hk] at hbranch
    obtain ⟨hcap,_,hnub⟩ := hbranch
    rw [RatPopulationCertificate.BranchBound,hk]
    apply local_population_lower_from_cap (cap:=(c.cap:ℝ)) hp (hz0.trans_le hz) hs0 (by exact_mod_cast hbd)
    · exact_mod_cast hcap
    · exact_mod_cast hnub
  | anchor =>
    rw [RatPopulationCertificate.BranchValid,hk] at hbranch
    obtain ⟨hraw,hce,hce1,hcem,hfactor,hgap,hbudget,hwhich⟩ := hbranch
    have hce0 : (0:ℝ) < (c.ce:ℝ) := by exact_mod_cast hce
    have hfac : (0:ℝ) ≤ (c.witness.factor:ℝ)+2 := by exact_mod_cast hfactor
    have hni : p*(z*R/p)=z*R := by field_simp
    have hcoun := anchor_population_count_balance (raw:=(c.raw:ℝ)) (slope:=(c.slope:ℝ))
      (intercept:=(c.intercept:ℝ)) hp (hz0.trans_le hz) hR0 hRl hW0 hWl hdm0 hL0.le hfac
      (by exact_mod_cast hitc) hni (by
        have hh := (Rat.cast_le (K:=ℝ)).mpr hbudget
        norm_num only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] at hh ⊢
        exact hh)
    rw [hni] at hcoun
    rw [RatPopulationCertificate.BranchBound,hk]
    refine ⟨?_,by
        have hh := (Rat.cast_le (K:=ℝ)).mpr hcem
        norm_num only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] at hh ⊢
        exact hh,hcoun,?_⟩
    · have hh : (c.ce:ℝ) ≤ 7/8 := by
        have hh := (Rat.cast_le (K:=ℝ)).mpr hce1
        norm_num only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] at hh ⊢
        exact hh
      linarith only [hh]
    · rcases hwhich with ⟨hfirst,hsecond⟩ | hsecond
      · apply le_max_of_le_left
        exact anchor_first_population_lower hp hz0 hz hW0.le hWl hRl hL0
          (by exact_mod_cast hb.le) (by exact_mod_cast hraw) (by exact_mod_cast hgap)
          (by
        have hh := (Rat.cast_le (K:=ℝ)).mpr hfirst
        norm_num only [Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_min] at hh ⊢
        exact hh) (by exact_mod_cast hsecond)
      · apply le_max_of_le_right
        exact anchor_second_population_lower (by exact_mod_cast hnu.le) hp hz0 hz hW0 hWl hdm0 hL0.le hfac
          hce0 hs0 (by exact_mod_cast hsecond)

end
end Cycle12
