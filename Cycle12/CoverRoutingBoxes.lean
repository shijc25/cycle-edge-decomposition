import Cycle12.CoverRoutingCoordinates

namespace Cycle12
open Real

theorem cover_fraction_ratio_mono {u U v V : ℝ} (hu₀ : 0 ≤ u) (hv : 0 < v) (hV : 0 < V)
    (hu : u ≤ U) (hVU : V ≤ v) : u/(v+u) ≤ U/(V+U) := by
  have hU := hu₀.trans hu
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul hu hVU hV.le hU]

noncomputable section

def coverRoutingDenomBox (coeff fan beta lo hi : ℝ) : ℝ :=
  coeff*coverScaleDen lo+fan*beta*coverScaleH hi*coverScaleW hi

def coverRoutingSizeLower (coeff lo hi s₀ Pl : ℝ) : ℝ :=
  (2*(43/10)^3)*coeff*Pl*s₀/(coverScaleW hi)^2

def coverRoutingFactorLower (coeff fan beta branch lo hi s₀ Pl : ℝ) : ℝ :=
  (2*(43/10)^3)*fan*beta*coverScaleH lo*branch*Pl*s₀/(coverScaleW hi*coverRoutingDenomBox coeff fan beta lo hi)

def coverRoutingPairBox (coeff lo hi s₀ Pl pu : ℝ) : ℝ :=
  coeff^2*(43/10)^3*(Pl)^2/(3*coverScaleW hi)-(11/3)*coeff*pu/s₀

def coverRoutingFanBox (coeff fan beta branch lo hi s₀ Pl pu : ℝ) : ℝ :=
  coeff*fan*beta*coverScaleH lo*branch*(43/10)^3*(Pl)^2/coverRoutingDenomBox coeff fan beta lo hi-
    (3*coverRoutingK coeff fan beta branch hi+1)*coeff*pu/(2*s₀)

theorem cover_routing_denom_box_pos {coeff fan beta lo hi : ℝ} (hc : 0 < coeff)
    (hf : 0 ≤ fan) (hb : 0 ≤ beta) (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hhim : hi ≤ (17/250)) :
    0 < coverRoutingDenomBox coeff fan beta lo hi := by
  have hd := cover_den_pos hlo (hlh.trans hhim)
  have hH := cover_h_pos (hlo.trans hlh)
  have hw := cover_w_nonneg hi
  unfold coverRoutingDenomBox
  positivity

theorem cover_routing_denom_le_box {coeff fan beta lo x hi : ℝ} (hc : 0 ≤ coeff)
    (hf : 0 ≤ fan) (hb : 0 ≤ beta) (hlo : 0 ≤ lo) (hlx : lo ≤ x) (hxh : x ≤ hi) :
    coverRoutingDenom coeff fan beta x ≤ coverRoutingDenomBox coeff fan beta lo hi := by
  have hd := mul_le_mul_of_nonneg_left (cover_den_antitone hlo hlx) hc
  have hm := mul_le_mul (cover_h_mono hxh) (cover_w_mono (hlo.trans hlx) hxh)
    (cover_w_nonneg x) (cover_h_pos ((hlo.trans hlx).trans hxh)).le
  have hf' := mul_le_mul_of_nonneg_left hm (mul_nonneg hf hb)
  unfold coverRoutingDenom coverRoutingDenomBox
  nlinarith

theorem cover_routing_k_mono {coeff fan beta branch x hi : ℝ} (hc : 0 < coeff)
    (hf : 0 ≤ fan) (hb : 0 ≤ beta) (hd : 0 ≤ branch)
    (hx : 0 ≤ x) (hxh : x ≤ hi) (hhim : hi ≤ (17/250)) :
    coverRoutingK coeff fan beta branch x ≤ coverRoutingK coeff fan beta branch hi := by
  have hdx := cover_den_pos hx (hxh.trans hhim)
  have hdh := cover_den_pos (hx.trans hxh) hhim
  have hH := cover_h_pos hx
  have hHh := cover_h_pos (hx.trans hxh)
  have hw := cover_w_nonneg x
  have hwh := cover_w_nonneg hi
  have hm := mul_le_mul (cover_h_mono hxh) (cover_w_mono hx hxh) hw hHh.le
  have hu : fan*beta*coverScaleH x*coverScaleW x ≤ fan*beta*coverScaleH hi*coverScaleW hi := by
    have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg hf hb)
    nlinarith
  have hden := mul_le_mul_of_nonneg_left (cover_den_antitone hx hxh) hc.le
  have hh := cover_fraction_ratio_mono (by positivity : 0 ≤ fan*beta*coverScaleH x*coverScaleW x)
    (mul_pos hc hdx) (mul_pos hc hdh) hu hden
  have hh' := mul_le_mul_of_nonneg_left hh (div_nonneg hd hc.le)
  have hDx : 0 < coeff*coverScaleDen x+fan*beta*coverScaleH x*coverScaleW x := by positivity
  have hDh : 0 < coeff*coverScaleDen hi+fan*beta*coverScaleH hi*coverScaleW hi := by positivity
  unfold coverRoutingK coverRoutingDenom
  convert hh' using 1 <;> field_simp <;> ring

theorem cover_routing_size_lower {coeff lo x hi s₀ s Pl P pu : ℝ} (hc : 0 ≤ coeff)
    (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x) (hxh : x ≤ hi)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hPl : 0 < Pl) (hPlo : Pl ≤ P) (hpu : P*coverScaleW x ≤ pu) :
    coverRoutingSizeLower coeff lo hi s₀ Pl ≤ coeff*coverRoutingQ x s P := by
  have hsp := hs₀.trans_le hs
  have hP₀ := hPl
  have hP := (hPl.trans_le hPlo)
  have hnum : (2*(43/10)^3)*coeff*Pl*s₀ ≤ (2*(43/10)^3)*coeff*P*s :=
    mul_le_mul (mul_le_mul_of_nonneg_left (hPlo) (by positivity)) hs hs₀.le (by positivity)
  have hden := pow_le_pow_left₀ (cover_w_nonneg x) (cover_w_mono hx.le hxh) 2
  have hh := (div_le_div_of_nonneg_right hnum (sq_nonneg (coverScaleW hi))).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (cover_w_pos hx)) hden)
  unfold coverRoutingSizeLower coverRoutingQ
  convert hh using 1 <;> ring

theorem cover_p_div_scale_upper {p pu s₀ s : ℝ} (hp : 0 ≤ p) (hpu : p ≤ pu)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) : p/s ≤ pu/s₀ := by
  have hsp := hs₀.trans_le hs
  exact (div_le_div_of_nonneg_right hpu hsp.le).trans
    (div_le_div_of_nonneg_left (hp.trans hpu) hs₀ hs)

theorem cover_routing_pair_box_lower {coeff lo x hi s₀ s Pl P pu : ℝ} (hc : 0 ≤ coeff)
    (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x) (hxh : x ≤ hi)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hPl : 0 < Pl) (hPlo : Pl ≤ P) (hpu : P*coverScaleW x ≤ pu) :
    coverRoutingPairBox coeff lo hi s₀ Pl pu ≤
      ((coeff*coverRoutingQ x s P)^2/3-(22/3)*(coeff*coverRoutingQ x s P))/coverRoutingAmbient x s := by
  have hsp := hs₀.trans_le hs
  have hP₀ := hPl
  have hP := (hPl.trans_le hPlo)
  have hw := cover_w_pos hx
  have hwh := cover_w_pos (hx.trans_le hxh)
  have hnum := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP₀.le (hPlo) 2)
    (show 0 ≤ coeff^2*(43/10)^3 by positivity)
  have hden := mul_le_mul_of_nonneg_left (cover_w_mono hx.le hxh) (by norm_num : (0:ℝ) ≤ 3)
  have hfirst : coeff^2*(43/10)^3*(Pl)^2/(3*coverScaleW hi) ≤ coeff^2*(43/10)^3*(P)^2/(3*coverScaleW x) :=
    (div_le_div_of_nonneg_right hnum (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  have hfee := mul_le_mul_of_nonneg_left (cover_p_div_scale_upper (mul_nonneg (hPl.trans_le hPlo).le (cover_w_nonneg x)) hpu hs₀ hs)
    (show 0 ≤ (11/3:ℝ)*coeff by positivity)
  have hfee' : (11/3:ℝ)*coeff*(P*coverScaleW x)/s ≤ (11/3:ℝ)*coeff*pu/s₀ := by
    convert hfee using 1 <;> ring
  rw [cover_routing_pair_normalized hx hsp]
  unfold coverRoutingPairBox
  linarith

theorem cover_routing_factor_lower {coeff fan beta branch lo x hi s₀ s Pl P pu : ℝ}
    (hc : 0 < coeff) (hf : 0 ≤ fan) (hb : 0 ≤ beta) (hd : 0 ≤ branch)
    (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x) (hxh : x ≤ hi) (hhim : hi ≤ (17/250))
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hPl : 0 < Pl) (hPlo : Pl ≤ P) (hpu : P*coverScaleW x ≤ pu) :
    coverRoutingFactorLower coeff fan beta branch lo hi s₀ Pl ≤
      coverRoutingK coeff fan beta branch x*(coeff*coverRoutingQ x s P) := by
  have hsp := hs₀.trans_le hs
  have hPl := hPl
  have hPx := (hPl.trans_le hPlo)
  have hHl := cover_h_pos hlo
  have hHx := cover_h_pos hx.le
  have hw := cover_w_pos hx
  have hwh := cover_w_pos (hx.trans_le hxh)
  have hden := cover_routing_denom_pos hc hf hb hx.le (hxh.trans hhim)
  have hbox := cover_routing_denom_box_pos hc hf hb hlo (hlx.trans hxh) hhim
  have hHP := mul_le_mul (cover_h_mono hlx) (hPlo) hPl.le hHx.le
  have hHPs := mul_le_mul hHP hs hs₀.le (mul_nonneg hHx.le hPx.le)
  have hnum : (2*(43/10)^3)*fan*beta*coverScaleH lo*branch*Pl*s₀ ≤
      (2*(43/10)^3)*fan*beta*coverScaleH x*branch*P*s := by
    have hh := mul_le_mul_of_nonneg_left hHPs
      (show 0 ≤ (2*(43/10)^3)*fan*beta*branch by positivity)
    convert hh using 1 <;> ring
  have hdenle := mul_le_mul (cover_w_mono hx.le hxh)
    (cover_routing_denom_le_box hc.le hf hb hlo hlx hxh) hden.le hwh.le
  rw [cover_routing_k_size hc hf hb hx (hxh.trans hhim)]
  unfold coverRoutingFactorLower
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hdenle)

theorem cover_routing_fan_box_lower {coeff fan beta branch lo x hi s₀ s Pl P pu : ℝ}
    (hc : 0 < coeff) (hf : 0 ≤ fan) (hb : 0 ≤ beta) (hd : 0 ≤ branch)
    (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x) (hxh : x ≤ hi) (hhim : hi ≤ (17/250))
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hPl : 0 < Pl) (hPlo : Pl ≤ P) (hpu : P*coverScaleW x ≤ pu) :
    coverRoutingFanBox coeff fan beta branch lo hi s₀ Pl pu ≤
      (coverRoutingK coeff fan beta branch x*(coeff*coverRoutingQ x s P)^2-
        (3*coverRoutingK coeff fan beta branch x+1)*(coeff*coverRoutingQ x s P))/coverRoutingAmbient x s := by
  have hsp := hs₀.trans_le hs
  have hPl := hPl
  have hPx := (hPl.trans_le hPlo)
  have hHl := cover_h_pos hlo
  have hHx := cover_h_pos hx.le
  have hden := cover_routing_denom_pos hc hf hb hx.le (hxh.trans hhim)
  have hbox := cover_routing_denom_box_pos hc hf hb hlo (hlx.trans hxh) hhim
  have hHP := mul_le_mul (cover_h_mono hlx)
    (pow_le_pow_left₀ hPl.le (hPlo) 2) (sq_nonneg _) hHx.le
  have hnum : coeff*fan*beta*coverScaleH lo*branch*(43/10)^3*(Pl)^2 ≤
      coeff*fan*beta*coverScaleH x*branch*(43/10)^3*(P)^2 := by
    have hh := mul_le_mul_of_nonneg_left hHP
      (show 0 ≤ coeff*fan*beta*branch*(43/10)^3 by positivity)
    convert hh using 1 <;> ring
  have hfirst := (div_le_div_of_nonneg_right hnum hbox.le).trans
    (div_le_div_of_nonneg_left (by positivity) hden
      (cover_routing_denom_le_box hc.le hf hb hlo hlx hxh))
  have hK := cover_routing_k_nonneg hc hf hb hd hx.le (hxh.trans hhim)
  have hKh := cover_routing_k_nonneg hc hf hb hd (hx.le.trans hxh) hhim
  have hKm := cover_routing_k_mono hc hf hb hd hx.le hxh hhim
  have hpx : 0 < P*coverScaleW x := mul_pos (hPl.trans_le hPlo) (cover_w_pos hx)
  have hfee₀ := mul_le_mul (by linarith : 3*coverRoutingK coeff fan beta branch x+1 ≤
      3*coverRoutingK coeff fan beta branch hi+1) (cover_p_div_scale_upper (mul_nonneg (hPl.trans_le hPlo).le (cover_w_nonneg x)) hpu hs₀ hs)
      (div_nonneg hpx.le hsp.le) (by positivity)
  have hfee : (3*coverRoutingK coeff fan beta branch x+1)*coeff*(P*coverScaleW x)/(2*s) ≤
      (3*coverRoutingK coeff fan beta branch hi+1)*coeff*pu/(2*s₀) := by
    have hh := mul_le_mul_of_nonneg_left hfee₀ (show 0 ≤ coeff/2 by positivity)
    convert hh using 1 <;> ring
  rw [cover_routing_fan_normalized hc hf hb hx (hxh.trans hhim) hsp]
  unfold coverRoutingFanBox
  linarith

end
end Cycle12
