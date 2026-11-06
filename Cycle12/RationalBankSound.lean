import Cycle12.RationalBankParameters

namespace Cycle12
open Real Cycle13
noncomputable section

/-- Rational gates and certified logarithms/exponentials imply every real
hypothesis used to construct the actual routing bank. -/
theorem rat_bank_parameters_sound (c : RatBankParameters) (hc : c.NumericValid)
    (hOrder : c.orderLog.Valid) (hStop : c.stopLog.Valid) (hBranch : c.branchLog.Valid)
    (hCut : c.cutDecay.Valid) (hCore : c.coreDecay.Valid) : c.realParameters.Valid := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28⟩ := hc
  have hOL := rat_scaled_log_upper_sound c.orderLog hOrder
  have hSL := rat_scaled_log_upper_sound c.stopLog hStop
  have hBL := rat_scaled_log_upper_sound c.branchLog hBranch
  have hCD := rat_decay_certificate_sound c.cutDecay hCut (1:ℝ) (by rw [h21]; norm_num)
  have hED := rat_decay_certificate_sound c.coreDecay hCore (1:ℝ) (by rw [h23]; norm_num)
  rw [h20] at hCD
  rw [h22] at hED
  simp only [mul_one] at hCD hED
  have hA : (0:ℝ) ≤ (c.cutExponent:ℝ) := by
    have hh : (0:ℚ) < c.cutExponent := by linarith only [h18,h19]
    exact_mod_cast hh.le
  have hgap : (0:ℝ) < ((c.cutExponent-2*c.orderLog.bound:ℚ):ℝ) := by exact_mod_cast h19
  have hcut := mul_le_mul_of_nonneg_left hCD (div_nonneg hA hgap.le)
  have hcut' :
      (c.cutExponent:ℝ)/((c.cutExponent-2*c.orderLog.bound:ℚ):ℝ)*
        exp (-((c.cutExponent-2*c.orderLog.bound:ℚ):ℝ)) ≤ (c.cutBound:ℝ) := by
    simpa only [RatBankParameters.cutBound,Rat.cast_mul,Rat.cast_div] using hcut
  have harg : 0 < c.nUpper := by
    have hp : (0:ℚ) < 2^c.orderLog.split := by positivity
    have hh := (le_div_iff₀ hp).mp hOrder.1
    rw [h17] at hh
    linarith only [hh,hp]
  have hBN := rat_bank_exp_of_log_bound (by exact_mod_cast harg : (0:ℝ) < (c.nUpper:ℝ))
    (by exact_mod_cast h25 : (0:ℝ) < (c.branchBound:ℝ))
    (a:=(c.branchExponent:ℝ)) (by
      rw [h26] at hBL
      have hh := hBL.trans ((Rat.cast_le (K:=ℝ)).mpr h27)
      simpa only [Rat.cast_div] using hh)
  refine ⟨rat_sampling_box_sound c.sample h0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [RatBankParameters.realParameters,RatSamplingBox.realBox]
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · have hh := (Rat.cast_lt (K:=ℝ)).mpr h7
    norm_num at hh ⊢
    exact hh
  · exact_mod_cast h8
  · exact_mod_cast h9
  · intro he
    have hh := (Rat.cast_le (K:=ℝ)).mpr (h10 he)
    simpa only [Rat.cast_mul,Rat.cast_ofNat,rat_bank_dc_cast,RatBankParameters.realParameters,RatSamplingBox.realBox, CoverBankParameters.dc,CoverBankParameters.ac] using hh
  · intro he
    have hh := (Rat.cast_le (K:=ℝ)).mpr (h11 he)
    simpa only [rat_bank_dc_cast,RatBankParameters.realParameters,RatSamplingBox.realBox, CoverBankParameters.dc,CoverBankParameters.ac] using hh
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h12
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_one,rat_bank_dc_cast,RatBankParameters.realParameters,RatSamplingBox.realBox, CoverBankParameters.dc,CoverBankParameters.ac] using hh
  · rcases h13 with he | hgain
    · left; exact_mod_cast he
    · right
      cases he : c.maximumScale with
      | none => simp only [he] at hgain
      | some sh =>
        simp only [he] at hgain
        refine ⟨(sh:ℝ),by simp [he],?_⟩
        have hh := (Rat.cast_le (K:=ℝ)).mpr hgain
        simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,rat_bank_ac_cast,RatBankParameters.realParameters,RatSamplingBox.realBox,CoverBankParameters.ac] using hh
  · intro he
    have hstop := h14 he
    cases hs : c.maximumScale with
    | none => simp only [hs] at hstop
    | some sh =>
      simp only [hs] at hstop
      refine ⟨(sh:ℝ),by simp [hs],?_⟩
      rw [hstop.1] at hSL
      have hm := mul_le_mul_of_nonneg_left hSL (show (0:ℝ) ≤ (c.coeff:ℝ) by exact_mod_cast h8.le)
      have hb := (Rat.cast_le (K:=ℝ)).mpr hstop.2
      push_cast at hm hb
      rw [rat_bank_ac_cast] at hb
      dsimp only [RatBankParameters.realParameters,CoverBankParameters.ac] at hb ⊢
      nlinarith only [hm,hb]
  · exact le_of_eq (rat_routing_q_cast _ _ _)
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h15
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,rat_cover_h_cast,rat_cover_den_cast,rat_cover_w_cast] using hh
  · exact_mod_cast h16
  · rw [h17] at hOL
    simpa only [RatBankParameters.nUpper,rat_routing_order_cast] using hOL
  · exact_mod_cast h18
  · have hh := (Rat.cast_lt (K:=ℝ)).mpr h19
    simpa only [RatBankParameters.cutExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_zero] using hh
  · simpa only [RatBankParameters.cutExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using hcut'
  · simpa only [RatBankParameters.coreExponent,RatBankParameters.qLower,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,rat_routing_q_cast,neg_mul] using hED
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h24
    simpa only [RatBankParameters.branchExponent,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_one,rat_bank_dc_cast,RatBankParameters.realParameters,RatSamplingBox.realBox, CoverBankParameters.dc,CoverBankParameters.ac] using hh
  · simpa only [RatBankParameters.nUpper,RatBankParameters.branchExponent,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_one,rat_bank_dc_cast,rat_routing_order_cast,RatBankParameters.realParameters,RatSamplingBox.realBox,CoverBankParameters.dc,CoverBankParameters.ac] using hBN
  · exact_mod_cast h28

end
end Cycle12
