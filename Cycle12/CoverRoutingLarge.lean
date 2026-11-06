import Cycle12.CoverRoutingBoxes

namespace Cycle12
open Real
noncomputable section

def coverRoutingLargeBox (a f beta eta Wlo pu s0 : ℝ) : ℝ := f*beta*eta*Wlo-a*pu/(2*s0)

theorem cover_routing_large_box_lower {a f beta eta Wlo pu x s P s0 : ℝ}
    (ha : 0 ≤ a) (hf : 0 ≤ f) (hb : 0 ≤ beta) (he : 0 ≤ eta)
    (hx : 0 < x) (hxm : x ≤ 17/250) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hP : 0 < P) (hpu : P*coverScaleW x ≤ pu) (hW : Wlo ≤ coverScaleWgt x s P) :
    coverRoutingLargeBox a f beta eta Wlo pu s0 ≤
      ((f*(beta*coverScaleZ x s P))*(eta*(P*coverScaleW x*coverRoutingAmbient x s))-
        a*coverRoutingQ x s P)/coverRoutingAmbient x s := by
  have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ f*beta*eta by positivity)
  have hfee := mul_le_mul_of_nonneg_left
    (cover_p_div_scale_upper (mul_nonneg hP.le (cover_w_nonneg x)) hpu hs0 hs)
    (show 0 ≤ a/2 by positivity)
  rw [cover_routing_large_normalized hx hxm (hs0.trans_le hs)]
  unfold coverRoutingLargeBox
  convert sub_le_sub hh hfee using 1 <;> ring

/-- One interval bound pays for the exact complement of the actual sample. -/
theorem cover_routing_complement_payment {n N bound actual pl p : ℝ}
    (hn : 0 < n) (hN : N=p*n) (hp : pl ≤ p)
    (hbound : 1-pl ≤ bound) (hactual : bound ≤ actual/n) : n-N ≤ actual := by
  have hdiv : 1-p ≤ actual/n := (by linarith only [hp,hbound] : 1-p ≤ bound).trans hactual
  have hm := (le_div_iff₀ hn).mp hdiv
  rw [hN]
  linarith only [hm]

end
end Cycle12
