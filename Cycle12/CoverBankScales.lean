import Cycle12.CoverDegreeTailScale

namespace Cycle12
open Real Cycle13
noncomputable section

def coverRoutingQ (x s P : ℝ) : ℝ := 2*(43/10)^3*P*s/(coverScaleW x)^2
def coverRoutingOrder (x s P : ℝ) : ℝ := 4*(43/10)^3*P*s^2/(coverScaleW x)^2

theorem cover_routing_order_identity (x s P : ℝ) :
    coverRoutingOrder x s P=2*s*coverRoutingQ x s P := by
  unfold coverRoutingOrder coverRoutingQ
  ring

theorem cover_routing_q_pos {x s P : ℝ} (hx : 0 < x) (hs : 0 < s) (hP : 0 < P) :
    0 < coverRoutingQ x s P := by unfold coverRoutingQ; positivity [cover_w_pos hx]

theorem cover_routing_order_pos {x s P : ℝ} (hx : 0 < x) (hs : 0 < s) (hP : 0 < P) :
    0 < coverRoutingOrder x s P := by unfold coverRoutingOrder; positivity [cover_w_pos hx]

theorem cover_routing_sample_identity {x s n P : ℝ} (hx : 0 < x)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) :
    (P*coverScaleW x)*n=coverRoutingOrder x s P := by
  have hw := cover_w_pos hx
  rw [hn]
  unfold coverRoutingOrder
  field_simp
  <;> ring

theorem cover_routing_q_mass {x s n m P : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) (hm : m=n^2/(2*s)) :
    (P*coverScaleW x)*m/n=coverRoutingQ x s P := by
  have hw := cover_w_pos hx
  have hn0 : 0 < n := by rw [hn]; positivity
  rw [hm]
  have hc : (P*coverScaleW x)*(n^2/(2*s))/n=(P*coverScaleW x)*n/(2*s) := by field_simp
  rw [hc,cover_routing_sample_identity hx hn,cover_routing_order_identity]
  field_simp

theorem cover_routing_edge_identity {x s n m P : ℝ} (hx : 0 < x) (hs : 0 < s)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3) (hm : m=n^2/(2*s)) :
    (P*coverScaleW x)^2*m=2*s*(coverRoutingQ x s P)^2 := by
  have hw := cover_w_pos hx
  rw [hm,hn]
  unfold coverRoutingQ
  field_simp
  <;> ring

theorem cover_routing_z_ratio {x s P : ℝ} (hx : 0 < x) (hs : 0 < s) (hP : 0 < P) :
    coverScaleZ x s P/coverRoutingQ x s P=coverScaleW x*coverScaleH x/coverScaleDen x := by
  have hw := cover_w_pos hx
  unfold coverScaleZ coverRoutingQ
  field_simp

theorem cover_routing_order_scaled_upper {x xh s0 s P upper : ℝ}
    (hx : 0 < x) (hxxh : x ≤ xh) (hs0 : 0 < s0) (hP : P ≤ upper) :
    coverRoutingOrder x s P ≤ coverRoutingOrder xh s0 upper*
      (coverScaleW xh/coverScaleW x)^2*(s/s0)^2 := by
  have hw := cover_w_pos hx
  have hwh := cover_w_pos (hx.trans_le hxxh)
  have he : coverRoutingOrder xh s0 upper*(coverScaleW xh/coverScaleW x)^2*(s/s0)^2=
      coverRoutingOrder x s upper := by
    unfold coverRoutingOrder
    field_simp
  rw [he]
  unfold coverRoutingOrder
  gcongr

theorem cover_routing_q_scaled_lower {x xh s0 s P lower q0 : ℝ}
    (hx : 0 < x) (hxxh : x ≤ xh) (hs0 : 0 < s0) (hs : 0 ≤ s) (hP : lower ≤ P)
    (hq0 : q0 ≤ coverRoutingQ xh s0 lower) :
    q0*(coverScaleW xh/coverScaleW x)^2*(s/s0) ≤ coverRoutingQ x s P := by
  have hw := cover_w_pos hx
  have hwh := cover_w_pos (hx.trans_le hxxh)
  have hh := mul_le_mul_of_nonneg_right hq0
    (show 0 ≤ (coverScaleW xh/coverScaleW x)^2*(s/s0) by positivity)
  have he : coverRoutingQ xh s0 lower*((coverScaleW xh/coverScaleW x)^2*(s/s0))=
      coverRoutingQ x s lower := by
    unfold coverRoutingQ
    field_simp
  rw [he] at hh
  have hlast : coverRoutingQ x s lower ≤ coverRoutingQ x s P := by unfold coverRoutingQ; gcongr
  simpa only [mul_assoc] using hh.trans hlast

theorem cover_bank_cut_tail {N : ℕ} {xl x xh s0 s lower P upper z0 ε dm ell : ℝ}
    (hN : 0 < N) (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hx : 0 < x) (hxxh : x ≤ xh)
    (hmax : xh ≤ 17/250) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 < lower) (hP : lower ≤ P) (hupper : P ≤ upper)
    (horder : (N:ℝ)=coverRoutingOrder x s P)
    (hz0 : z0 ≤ 2*(43/10)^3*lower*coverScaleH xl*s0/(coverScaleW xh*coverScaleDen xl))
    (hdm : 0 ≤ dm) (hlog : log (coverRoutingOrder xh s0 upper) ≤ ell)
    (hell : 2 ≤ ell) (hgap : 0 < 2*ε^2*dm*z0-2*ell) :
    0 < 2*ε^2*(dm*coverScaleZ x s P)-2*log (N:ℝ) ∧
      sharpCutFailure N ε (dm*coverScaleZ x s P) ≤
        (2*ε^2*dm*z0)/(2*ε^2*dm*z0-2*ell)*exp (-(2*ε^2*dm*z0-2*ell)) := by
  have hu : 1 ≤ coverScaleW xh/coverScaleW x :=
    (one_le_div (cover_w_pos hx)).mpr (cover_w_mono hx.le hxxh)
  have ht : 1 ≤ s/s0 := (one_le_div hs0).mpr hss
  have hz := cover_scaled_z_lower hxl hxlx hx hxxh hmax hs0 hss hlower.le hP hz0
  refine sharp_cut_failure_two_scale (k:=2) (j:=2) hN
    (cover_routing_order_pos (hx.trans_le hxxh) hs0 ((hlower.trans_le hP).trans_le hupper)) hu ht
    ?_ hlog hell hell hgap ?_
  · rw [horder]
    exact cover_routing_order_scaled_upper hx hxxh hs0 hupper
  · have hh := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2*ε^2*dm by positivity)
    nlinarith only [hh]

end
end Cycle12
