import Cycle12.CoverDegreeTailScale
import Cycle12.CoverSampleRealization
import Cycle12.FixedSampleTails

namespace Cycle12
open Finset Real Cycle13 SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable

theorem cover_degree_certificate_sound (c : CoverSamplingBox) (hc : c.Valid)
    {dm mu zbase rate bound : ℝ} (hdm : 0 < dm) (hgap : dm < mu)
    (hmu : mu ≤ coverScaleMu c.xl)
    (hzbase : zbase ≤ 2*(43/10)^3*c.Plo*coverScaleH c.xl*c.s0/(coverScaleW c.xh*coverScaleDen c.xl))
    (hrate0 : 0 ≤ rate) (hrate : rate ≤ mu-dm-dm*log (mu/dm))
    (hscale : 3 ≤ rate*zbase)
    (hbound : (4*(43/10)^3*c.s0^2/(coverScaleW c.xh)^3)*exp (-rate*zbase) ≤ bound)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {x s : ℝ} {k : ℕ} (hx : 0 < x) (hxl : c.xl ≤ x) (hxh : x ≤ c.xh) (hs : c.s0 ≤ s)
    (hn : (Fintype.card V:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3)
    (hk : k=⌊coverSampleP x*(Fintype.card V:ℝ)⌋₊)
    (hmean : ∀ v, coverScaleMu x*coverScaleZ x s (((k:ℝ)/(Fintype.card V:ℝ))/coverScaleW x) ≤
      ((k:ℝ)/(Fintype.card V:ℝ))*(neighborsIn G v univ).card) :
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun T => ∃ v, ((neighborsIn G v T).card:ℝ) ≤
        dm*coverScaleZ x s (((k:ℝ)/(Fintype.card V:ℝ))/coverScaleW x)) ≤ bound := by
  let p : ℝ := (k:ℝ)/(Fintype.card V:ℝ)
  let P : ℝ := p/coverScaleW x
  have hs0 : 0 < c.s0 := by linarith only [hc.density_lower]
  have hspos := hs0.trans_le hs
  have hw := cover_w_pos hx
  have hH := cover_h_pos hx.le
  have hden := cover_den_pos hx.le (hxh.trans hc.xmax)
  obtain ⟨hnlo,hNlo,hPl,hPu,hpl,hpsample,hp0,hphalf⟩ :=
    cover_sampling_box_realizes c hc hx hxl hxh hs hn hk (p:=p) rfl (P:=P) rfl
  have hn4R : (4:ℝ) ≤ Fintype.card V := hc.order_four.trans hnlo
  have hn0R : (0:ℝ) < Fintype.card V := by linarith only [hn4R]
  have hn0 : 0 < Fintype.card V := by exact_mod_cast hn0R
  letI : Nonempty V := Fintype.card_pos_iff.mp hn0
  have hklt : k < Fintype.card V := by
    have hh : (k:ℝ) < Fintype.card V := (div_lt_one hn0R).mp (hphalf.trans (by norm_num))
    exact_mod_cast hh
  have hPpos := hc.ratio_positive.trans_le hPl
  have hz : 0 < coverScaleZ x s P := by unfold coverScaleZ; positivity
  have hmuactual := hmu.trans (cover_mu_mono hc.xl_nonneg hxl)
  have hm (v : V) : mu*coverScaleZ x s P ≤ p*(neighborsIn G v univ).card :=
    (mul_le_mul_of_nonneg_right hmuactual hz.le).trans (hmean v)
  have hh := fixed_sample_degree_failure G hklt.le hz hdm hgap hm
  have he : exp (-(mu-dm-dm*log (mu/dm))*coverScaleZ x s P) ≤ exp (-rate*coverScaleZ x s P) := by
    apply exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hrate hz.le
    nlinarith only [hm]
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (Fintype.card V))).trans
  exact (cover_degree_uniform_scale hc.xl_nonneg hxl hx hxh hc.xmax hs0 hs
    hc.ratio_positive.le hPl hzbase hrate0 hscale hn).trans hbound

end
end Cycle12
