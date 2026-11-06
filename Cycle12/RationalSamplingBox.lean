import Cycle12.RationalMomentCertificate

namespace Cycle12

structure RatSamplingBox where
  xl : ℚ
  xh : ℚ
  s0 : ℚ
  Plo : ℚ
  Pu : ℚ
  nlo : ℚ
  Nlo : ℚ
  pl : ℚ

def RatSamplingBox.Valid (c : RatSamplingBox) : Prop :=
  0 ≤ c.xl ∧ c.xl ≤ c.xh ∧ c.xh ≤ 17/250 ∧ 1 ≤ c.s0 ∧ 0 < c.Plo ∧
  4 ≤ c.nlo ∧ 1 ≤ c.Nlo ∧
  c.Plo ≤ ratCoverP0 c.xl-(ratCoverW c.xh)^2/(4*(43/10)^3*c.s0^2) ∧
  ratCoverP0 c.xh ≤ c.Pu ∧
  c.nlo ≤ 4*(43/10)^3*c.s0^2/(ratCoverW c.xh)^3 ∧
  c.Nlo ≤ 4*(43/10)^3*c.Plo*c.s0^2/(ratCoverW c.xh)^2 ∧ c.pl ≤ c.Plo*ratCoverW c.xl

instance instDecidableRatSamplingBoxValid (c : RatSamplingBox) : Decidable c.Valid := by
  unfold RatSamplingBox.Valid
  infer_instance

def RatSamplingBox.realBox (c : RatSamplingBox) : CoverSamplingBox :=
  ⟨c.xl,c.xh,c.s0,c.Plo,c.Pu,c.nlo,c.Nlo,c.pl⟩

theorem rat_sampling_box_sound (c : RatSamplingBox) (hc : c.Valid) : c.realBox.Valid := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := hc
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [RatSamplingBox.realBox]
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

end Cycle12
