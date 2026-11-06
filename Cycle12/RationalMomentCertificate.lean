import Cycle12.CoverMomentCertificate

namespace Cycle12

def ratCoverW (x : ℚ) : ℚ := (43/10)^3*x^2
def ratCoverV (x : ℚ) : ℚ := ratCoverW x*(1+3*x)
def ratCoverP0 (x : ℚ) : ℚ := (1+3*x)*(99/200+11/100*ratCoverV x+7/100*(ratCoverV x)^2)
def ratCoverGap (v : ℚ) : ℚ :=
  1/100+1001/40000*v-311/10000*v^2+407/5000*v^3+77/5000*v^4+49/10000*v^5
def ratOrderFactor (n : ℚ) : ℚ := (n/(n-2))^3

theorem rat_cover_w_cast (x : ℚ) : (ratCoverW x:ℝ)=coverScaleW (x:ℝ) := by
  norm_num [ratCoverW,coverScaleW]
theorem rat_cover_v_cast (x : ℚ) : (ratCoverV x:ℝ)=coverSampleV (x:ℝ) := by
  norm_num [ratCoverV,rat_cover_w_cast,cover_v_w_identity]
theorem rat_cover_p0_cast (x : ℚ) : (ratCoverP0 x:ℝ)=coverScaleP0 (x:ℝ) := by
  norm_num [ratCoverP0,rat_cover_v_cast,coverScaleP0,coverScaleA]
theorem rat_cover_gap_cast (v : ℚ) : (ratCoverGap v:ℝ)=coverIncidentGap (v:ℝ) := by
  norm_num [ratCoverGap,coverIncidentGap]
theorem rat_order_factor_cast (n : ℚ) : (ratOrderFactor n:ℝ)=finiteOrderVarianceFactor (n:ℝ) := by
  norm_num [ratOrderFactor,finiteOrderVarianceFactor]

structure RatMomentCertificate where
  xl : ℚ
  xh : ℚ
  s0 : ℚ
  Plo : ℚ
  Pu : ℚ
  nlo : ℚ
  Nlo : ℚ
  pl : ℚ
  density : ℚ
  edgeVariance : ℚ
  incidentVariance : ℚ
  edgeGap : ℚ
  incidentGap : ℚ

def RatMomentCertificate.Valid (c : RatMomentCertificate) : Prop :=
  0 ≤ c.xl ∧ c.xl ≤ c.xh ∧ c.xh ≤ 17/250 ∧ 1 ≤ c.s0 ∧ 0 < c.Plo ∧
  4 ≤ c.nlo ∧ 1 ≤ c.Nlo ∧
  c.Plo ≤ ratCoverP0 c.xl-(ratCoverW c.xh)^2/(4*(43/10)^3*c.s0^2) ∧
  ratCoverP0 c.xh ≤ c.Pu ∧
  c.nlo ≤ 4*(43/10)^3*c.s0^2/(ratCoverW c.xh)^3 ∧
  c.Nlo ≤ 4*(43/10)^3*c.Plo*c.s0^2/(ratCoverW c.xh)^2 ∧
  c.pl ≤ c.Plo*ratCoverW c.xl ∧
  (if c.s0 ≤ 2 then 1/4 else (c.s0-1)/c.s0^2) ≤ c.density ∧
  (1-c.pl)*(ratCoverW c.xh)^2*c.density*ratOrderFactor c.nlo/(2*(43/10)^3*c.Plo) ≤ c.edgeVariance ∧
  c.Pu*(ratCoverW c.xh)^2*(1-c.pl)^3*c.density*ratOrderFactor c.nlo/(2*(43/10)^3) ≤ c.incidentVariance ∧
  c.edgeGap ≤ 3/100-1/(c.Nlo*(1-1/c.nlo)) ∧
  c.incidentGap ≤ (1+3*c.xl)*ratCoverGap (ratCoverV c.xl)-c.Pu/(c.nlo-1) ∧
  0 < c.edgeGap ∧ 0 < c.incidentGap

instance instDecidableRatMomentCertificateValid (c : RatMomentCertificate) : Decidable c.Valid := by
  unfold RatMomentCertificate.Valid
  infer_instance

def RatMomentCertificate.realCertificate (c : RatMomentCertificate) : CoverMomentCertificate :=
  ⟨⟨c.xl,c.xh,c.s0,c.Plo,c.Pu,c.nlo,c.Nlo,c.pl⟩,
    c.density,c.edgeVariance,c.incidentVariance,c.edgeGap,c.incidentGap⟩

theorem rat_moment_certificate_valid (c : RatMomentCertificate) (hc : c.Valid) :
    c.realCertificate.Valid := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18⟩ := hc
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [RatMomentCertificate.realCertificate]
  · exact_mod_cast h0
  · exact_mod_cast h1
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h2
    norm_num at hh ⊢
    exact hh
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h7
    simpa only [rat_cover_p0_cast,rat_cover_w_cast,Rat.cast_sub,Rat.cast_pow,Rat.cast_mul,
      Rat.cast_div,Rat.cast_ofNat] using hh
  · simpa only [rat_cover_p0_cast] using (Rat.cast_le (K:=ℝ)).mpr h8
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h9
    simpa only [rat_cover_w_cast,Rat.cast_pow,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h10
    simpa only [rat_cover_w_cast,Rat.cast_pow,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h11
    simpa only [rat_cover_w_cast,Rat.cast_mul] using hh
  · change (if (c.s0:ℝ) ≤ 2 then (1/4:ℝ) else ((c.s0:ℝ)-1)/(c.s0:ℝ)^2) ≤ (c.density:ℝ)
    by_cases h : c.s0 ≤ 2
    · have hR : (c.s0:ℝ) ≤ 2 := by exact_mod_cast h
      rw [if_pos hR]
      rw [if_pos h] at h12
      have hh := (Rat.cast_le (K:=ℝ)).mpr h12
      norm_num at hh ⊢
      exact hh
    · have hR : ¬ (c.s0:ℝ) ≤ 2 := by exact_mod_cast h
      rw [if_neg hR]
      rw [if_neg h] at h12
      have hh := (Rat.cast_le (K:=ℝ)).mpr h12
      norm_num at hh ⊢
      exact hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h13
    simpa only [rat_cover_w_cast,rat_order_factor_cast,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h14
    simpa only [rat_cover_w_cast,rat_order_factor_cast,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h15
    norm_num at hh ⊢
    exact hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h16
    simpa only [rat_cover_gap_cast,rat_cover_v_cast,Rat.cast_add,Rat.cast_sub,Rat.cast_one,
      Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hh
  · exact_mod_cast h17
  · exact_mod_cast h18

end Cycle12
