import Cycle12.CoverBankAlgebra
import Cycle12.Foundations.CertifiedCycleCapacity

namespace Cycle12
open Real
noncomputable section

def coverRoutingAmbient (x s : ℝ) : ℝ := 4*(43/10)^3*s^2/(coverScaleW x)^3
def coverRoutingDenom (a f b x : ℝ) : ℝ := a*coverScaleDen x+f*b*coverScaleH x*coverScaleW x
def coverRoutingK (a f b d x : ℝ) : ℝ :=
  f*b*coverScaleH x*coverScaleW x*d/(a*coverRoutingDenom a f b x)

theorem cover_routing_ambient_pos {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    0 < coverRoutingAmbient x s := by unfold coverRoutingAmbient; positivity [cover_w_pos hx]

theorem cover_routing_denom_pos {a f b x : ℝ} (ha : 0 < a) (hf : 0 ≤ f) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hxm : x ≤ 17/250) : 0 < coverRoutingDenom a f b x := by
  unfold coverRoutingDenom
  positivity [cover_den_pos hx hxm,cover_h_pos hx,cover_w_nonneg x]

theorem cover_routing_k_nonneg {a f b d x : ℝ} (ha : 0 < a) (hf : 0 ≤ f) (hb : 0 ≤ b)
    (hd : 0 ≤ d) (hx : 0 ≤ x) (hxm : x ≤ 17/250) : 0 ≤ coverRoutingK a f b d x := by
  unfold coverRoutingK
  positivity [cover_routing_denom_pos ha hf hb hx hxm,cover_h_pos hx,cover_w_nonneg x]

theorem cover_routing_q_div_order {x s P : ℝ} (hx : 0 < x) (hs : 0 < s) :
    coverRoutingQ x s P/coverRoutingAmbient x s=(P*coverScaleW x)/(2*s) := by
  have hw := (cover_w_pos hx).ne'
  unfold coverRoutingQ coverRoutingAmbient
  field_simp
  <;> ring

theorem cover_routing_q_sq_div_order {x s P : ℝ} (hx : 0 < x) (hs : 0 < s) :
    (coverRoutingQ x s P)^2/coverRoutingAmbient x s=(43/10)^3*P^2/coverScaleW x := by
  have hw := (cover_w_pos hx).ne'
  unfold coverRoutingQ coverRoutingAmbient
  field_simp
  <;> ring

theorem cover_routing_k_budget {a f b d x s P : ℝ} (ha : 0 < a) (hf : 0 ≤ f) (hb : 0 ≤ b)
    (hx : 0 < x) (hxm : x ≤ 17/250) :
    coverRoutingK a f b d x*(a*coverRoutingQ x s P)*
      (a*coverRoutingQ x s P+f*(b*coverScaleZ x s P))=
      (f*(b*coverScaleZ x s P))*(d*coverRoutingQ x s P) := by
  have hden := (cover_routing_denom_pos ha hf hb hx.le hxm).ne'
  have hd := (cover_den_pos hx.le hxm).ne'
  have hw := (cover_w_pos hx).ne'
  have ha' := ha.ne'
  unfold coverRoutingK coverRoutingQ coverScaleZ
  field_simp
  unfold coverRoutingDenom
  ring

theorem cover_routing_k_size_sq_div_order {a f b d x s P : ℝ} (ha : 0 < a)
    (hf : 0 ≤ f) (hb : 0 ≤ b) (hx : 0 < x) (hxm : x ≤ 17/250) (hs : 0 < s) :
    coverRoutingK a f b d x*(a*coverRoutingQ x s P)^2/coverRoutingAmbient x s=
      a*f*b*coverScaleH x*d*(43/10)^3*P^2/coverRoutingDenom a f b x := by
  have hden := (cover_routing_denom_pos ha hf hb hx.le hxm).ne'
  have hw := (cover_w_pos hx).ne'
  have ha' := ha.ne'
  have hs' := hs.ne'
  unfold coverRoutingK coverRoutingQ coverRoutingAmbient
  field_simp
  <;> ring

theorem cover_routing_k_size {a f b d x s P : ℝ} (ha : 0 < a)
    (hf : 0 ≤ f) (hb : 0 ≤ b) (hx : 0 < x) (hxm : x ≤ 17/250) :
    coverRoutingK a f b d x*(a*coverRoutingQ x s P)=
      2*(43/10)^3*f*b*coverScaleH x*d*P*s/(coverScaleW x*coverRoutingDenom a f b x) := by
  have hden := (cover_routing_denom_pos ha hf hb hx.le hxm).ne'
  have hw := (cover_w_pos hx).ne'
  have ha' := ha.ne'
  unfold coverRoutingK coverRoutingQ
  field_simp
  <;> ring

theorem cover_routing_pair_normalized {a x s P : ℝ} (hx : 0 < x) (hs : 0 < s) :
    ((a*coverRoutingQ x s P)^2/3-(22/3)*(a*coverRoutingQ x s P))/coverRoutingAmbient x s=
      a^2*(43/10)^3*P^2/(3*coverScaleW x)-(11/3)*a*(P*coverScaleW x)/s := by
  have hw := (cover_w_pos hx).ne'
  have hs' := hs.ne'
  unfold coverRoutingQ coverRoutingAmbient
  field_simp
  <;> ring

theorem cover_routing_fan_normalized {a f b d x s P : ℝ} (ha : 0 < a)
    (hf : 0 ≤ f) (hb : 0 ≤ b) (hx : 0 < x) (hxm : x ≤ 17/250) (hs : 0 < s) :
    (coverRoutingK a f b d x*(a*coverRoutingQ x s P)^2-
      (3*coverRoutingK a f b d x+1)*(a*coverRoutingQ x s P))/coverRoutingAmbient x s=
      a*f*b*coverScaleH x*d*(43/10)^3*P^2/coverRoutingDenom a f b x-
      (3*coverRoutingK a f b d x+1)*a*(P*coverScaleW x)/(2*s) := by
  rw [sub_div,cover_routing_k_size_sq_div_order ha hf hb hx hxm hs]
  have hr := cover_routing_q_div_order (P:=P) hx hs
  congr 1
  calc
    _ = ((3*coverRoutingK a f b d x+1)*a)*(coverRoutingQ x s P/coverRoutingAmbient x s) := by ring
    _ = _ := by rw [hr]; ring

theorem cover_routing_large_normalized {a f b eta x s P : ℝ}
    (hx : 0 < x) (hxm : x ≤ 17/250) (hs : 0 < s) :
    ((f*(b*coverScaleZ x s P))*(eta*(P*coverScaleW x*coverRoutingAmbient x s))-
      a*coverRoutingQ x s P)/coverRoutingAmbient x s=
      f*b*eta*coverScaleWgt x s P-a*(P*coverScaleW x)/(2*s) := by
  have hn := (cover_routing_ambient_pos hx hs).ne'
  have hd := (cover_den_pos hx.le hxm).ne'
  have hw := (cover_w_pos hx).ne'
  have hs' := hs.ne'
  unfold coverScaleZ coverScaleWgt coverRoutingQ coverRoutingAmbient
  field_simp
  <;> ring

end
end Cycle12
