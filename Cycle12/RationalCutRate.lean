import Cycle12.CoverTruncationCoordinates

namespace Cycle12
open Finset Cycle13

def ratJansonPhiSixteen (tau : ℚ) : ℚ :=
  ∑ k ∈ range 15, (1-tau)^(k+2)/(((k:ℚ)+2)*((k:ℚ)+1))

def ratCoverJansonDenominator (lambda kappa nu pmax zlo ps : ℚ) : ℚ :=
  min (lambda+1) (lambda+pmax/(nu*zlo)+kappa/(lambda*nu))+1/(ps*nu*zlo)

theorem rat_janson_phi_sixteen_cast (tau : ℚ) :
    (ratJansonPhiSixteen tau:ℝ)=jansonPhiPolynomial 15 (1-(tau:ℝ)) := by
  simp only [ratJansonPhiSixteen,jansonPhiPolynomial,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,
    Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]

theorem rat_cover_janson_denominator_cast (lambda kappa nu pmax zlo ps : ℚ) :
    (ratCoverJansonDenominator lambda kappa nu pmax zlo ps:ℝ)=
      coverJansonDenominator lambda kappa nu pmax zlo ps := by
  simp only [ratCoverJansonDenominator,coverJansonDenominator,Rat.cast_min,Rat.cast_add,
    Rat.cast_div,Rat.cast_mul,Rat.cast_one]

structure RatCutRateCertificate where
  lambda : ℚ
  kappa : ℚ
  nu : ℚ
  pmax : ℚ
  zlo : ℚ
  ps : ℚ
  tau : ℚ
  phi : ℚ
  gamma : ℚ

def RatCutRateCertificate.Valid (c : RatCutRateCertificate) : Prop :=
  1 ≤ c.lambda ∧ 0 < c.kappa ∧ 0 < c.nu ∧ 0 < c.pmax ∧ 0 < c.zlo ∧ 0 < c.ps ∧
  0 < c.tau ∧ c.tau ≤ 1 ∧ 0 ≤ c.phi ∧ 0 < c.gamma ∧
  c.phi ≤ ratJansonPhiSixteen c.tau ∧
  c.gamma ≤ c.phi*c.kappa*c.ps/ratCoverJansonDenominator c.lambda c.kappa c.nu c.pmax c.zlo c.ps

instance instDecidableRatCutRateValid (c : RatCutRateCertificate) : Decidable c.Valid := by
  unfold RatCutRateCertificate.Valid
  infer_instance

noncomputable section

def RatCutRateCertificate.Sound (c : RatCutRateCertificate) : Prop :=
  ∀ p z residual u : ℝ, 0 < p → p ≤ (c.pmax:ℝ) → (c.zlo:ℝ) ≤ z →
    (c.ps:ℝ)*p ≤ residual → (c.nu:ℝ)*(z/p) ≤ u →
    (c.gamma:ℝ)*z ≤ fullJansonPhi (c.tau:ℝ)*((c.kappa:ℝ)*(z/p)*u)*residual^2/
      (1+min (((c.lambda:ℝ)+1)*u) ((c.lambda:ℝ)*u+1+((c.kappa:ℝ)*(z/p)*u)/((c.lambda:ℝ)*u))*residual)

theorem rat_cut_rate_certificate_sound (c : RatCutRateCertificate) (hc : c.Valid) : c.Sound := by
  obtain ⟨hl,hk,hn,hp,hz,hps,ht0,ht1,hphi0,hg,hphi,hgamma⟩ := hc
  have hphiR : (c.phi:ℝ) ≤ fullJansonPhi (c.tau:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hphi
    rw [rat_janson_phi_sixteen_cast] at hh
    exact hh.trans (full_janson_phi_series_lower 15 (c.tau:ℝ) (by exact_mod_cast ht0) (by exact_mod_cast ht1))
  have hgammaR : (c.gamma:ℝ) ≤ (c.phi:ℝ)*(c.kappa:ℝ)*(c.ps:ℝ)/
      coverJansonDenominator c.lambda c.kappa c.nu c.pmax c.zlo c.ps := by
    simpa only [Rat.cast_div,Rat.cast_mul,rat_cover_janson_denominator_cast]
      using (Rat.cast_le (K:=ℝ)).mpr hgamma
  have hphi0R : (0:ℝ) ≤ (c.phi:ℝ) := by exact_mod_cast hphi0
  have hlR : (1:ℝ) ≤ (c.lambda:ℝ) := by exact_mod_cast hl
  have hkR : (0:ℝ) ≤ (c.kappa:ℝ) := by exact_mod_cast hk.le
  have hnR : (0:ℝ) < (c.nu:ℝ) := by exact_mod_cast hn
  have hzR : (0:ℝ) < (c.zlo:ℝ) := by exact_mod_cast hz
  have hpsR : (0:ℝ) < (c.ps:ℝ) := by exact_mod_cast hps
  intro p z residual u hp0 hpu hzlo hres hu
  have hzp := hzR.trans_le hzlo
  have hres0 := (mul_pos hpsR hp0).trans_le hres
  have hh := cover_janson_rate_lower hphi0R hlR hkR hnR hp0 hpu hzR hzlo hpsR hres hgammaR
  exact hh.trans (rounded_janson_rate_lower hphi0R hphiR hlR hkR (div_pos hzp hp0).le hres0
    (mul_pos hnR (div_pos hzp hp0)) hu)

end
end Cycle12
