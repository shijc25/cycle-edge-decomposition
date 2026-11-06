import Cycle12.CoverSamplingEnvelope

namespace Cycle12
noncomputable section

structure CoverSamplingBox where
  xl : ℝ
  xh : ℝ
  s0 : ℝ
  Plo : ℝ
  Pu : ℝ
  nlo : ℝ
  Nlo : ℝ
  pl : ℝ

structure CoverSamplingBox.Valid (c : CoverSamplingBox) : Prop where
  xl_nonneg : 0 ≤ c.xl
  ordered : c.xl ≤ c.xh
  xmax : c.xh ≤ 17/250
  density_lower : 1 ≤ c.s0
  ratio_positive : 0 < c.Plo
  order_four : 4 ≤ c.nlo
  sample_one : 1 ≤ c.Nlo
  ratio_lower : c.Plo ≤ coverScaleP0 c.xl-(coverScaleW c.xh)^2/(4*(43/10)^3*c.s0^2)
  ratio_upper : coverScaleP0 c.xh ≤ c.Pu
  order_lower : c.nlo ≤ 4*(43/10)^3*c.s0^2/(coverScaleW c.xh)^3
  sample_lower : c.Nlo ≤ 4*(43/10)^3*c.Plo*c.s0^2/(coverScaleW c.xh)^2
  probability_lower : c.pl ≤ c.Plo*coverScaleW c.xl

/-- All bounds refer to the actual floor sample. The upper sampling fraction
is proved throughout the interval, rather than assumed at numeric endpoints. -/
theorem cover_sampling_box_realizes (c : CoverSamplingBox) (hc : c.Valid)
    {x s n p P : ℝ} {k : ℕ} (hx : 0 < x) (hxl : c.xl ≤ x) (hxh : x ≤ c.xh)
    (hs : c.s0 ≤ s) (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3)
    (hk : k=⌊coverSampleP x*n⌋₊) (hp : p=(k:ℝ)/n) (hP : P=p/coverScaleW x) :
    c.nlo ≤ n ∧ c.Nlo ≤ (k:ℝ) ∧ c.Plo ≤ P ∧ P ≤ c.Pu ∧
    c.pl ≤ p ∧ p ≤ coverSampleP x ∧ 0 < p ∧ p < 1/2 := by
  have hs0 : 0 < c.s0 := by linarith only [hc.density_lower]
  have hw := cover_w_pos hx
  have hspos := hs0.trans_le hs
  have hnpos : 0 < n := by rw [hn]; positivity
  have hnlow := hc.order_lower.trans (cover_order_lower hx hxh hs0 hs hn)
  have hPexpr : P=(⌊coverSampleP x*n⌋₊:ℝ)/(n*coverScaleW x) := by
    rw [hP,hp,hk,div_div]
  have hpbox := cover_floor_parameter_envelope hc.xl_nonneg hxl hx hxh hs0 hs hn
  rw [← hPexpr] at hpbox
  have hPl := hc.ratio_lower.trans hpbox.1
  have hPu := hpbox.2.trans hc.ratio_upper
  have hN := hc.sample_lower.trans (cover_sample_order_lower hx hxh hs0 hs hc.ratio_positive.le hPl hn)
  have hid : P*coverScaleW x*n=(k:ℝ) := by rw [hP,hp]; field_simp
  rw [hid] at hN
  have hprob := (cover_sample_probability_envelope hc.xl_nonneg hxl hxh
    hc.ratio_positive.le hPl hPu).1
  have hidP : P*coverScaleW x=p := by rw [hP]; field_simp
  rw [hidP] at hprob
  have hkposR : (0:ℝ) < k := by linarith only [hc.sample_one,hN]
  have hp0 : 0 < p := by rw [hp]; exact div_pos hkposR hnpos
  have hpactual : p ≤ coverSampleP x := by
    rw [hp]
    apply (div_le_iff₀ hnpos).mpr
    rw [hk]
    apply Nat.floor_le
    exact mul_nonneg (cover_sample_p_lt_half x hx.le (hxh.trans hc.xmax)).1 hnpos.le
  exact ⟨hnlow,hN,hPl,hPu,hc.probability_lower.trans hprob,hpactual,hp0,
    hpactual.trans_lt (cover_sample_p_lt_half x hx.le (hxh.trans hc.xmax)).2⟩

end
end Cycle12
