import Cycle12.CoverBankScales

namespace Cycle12
open Real Cycle13
noncomputable section

/-- The union over all sample vertices is controlled on the entire
x interval and density ray, despite the changing floor sample order. -/
theorem cover_bank_branch_tail {N : ℕ} {x xh s0 s lower P upper q0 dc mean g : ℝ}
    (hx : 0 < x) (hxxh : x ≤ xh) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 < lower) (hP : lower ≤ P) (hupper : P ≤ upper)
    (horder : (N:ℝ)=coverRoutingOrder x s P)
    (hq0 : q0 ≤ coverRoutingQ xh s0 lower) (hdc : 0 ≤ dc) (hg : g < 1)
    (hscale : 2 ≤ 2*dc*q0*(mean-g)^2/(1-g)) :
    (N:ℝ)*exp (-2*(dc*coverRoutingQ x s P)*(mean-g)^2/(1-g)) ≤
      coverRoutingOrder xh s0 upper*exp (-(2*dc*q0*(mean-g)^2/(1-g))) := by
  let v := coverScaleW xh/coverScaleW x
  let t := s/s0
  let a := 2*dc*q0*(mean-g)^2/(1-g)
  have hv : 1 ≤ v := (one_le_div (cover_w_pos hx)).mpr (cover_w_mono hx.le hxxh)
  have ht : 1 ≤ t := (one_le_div hs0).mpr hss
  have hN := cover_routing_order_pos (hx.trans_le hxxh) hs0 ((hlower.trans_le hP).trans_le hupper)
  have hnn : (N:ℝ) ≤ coverRoutingOrder xh s0 upper*(v^2)*t^2 := by
    rw [horder]
    exact cover_routing_order_scaled_upper hx hxxh hs0 hupper
  have hQ := cover_routing_q_scaled_lower hx hxxh hs0 (hs0.trans_le hss).le hP hq0
  have he : a*v^2*t ≤ 2*(dc*coverRoutingQ x s P)*(mean-g)^2/(1-g) := by
    have hh := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2*dc*(mean-g)^2/(1-g) by positivity)
    dsimp only [a,v,t]
    convert hh using 1 <;> ring
  have hexp : exp (-2*(dc*coverRoutingQ x s P)*(mean-g)^2/(1-g)) ≤ exp (-a*v^2*t) := by
    apply exp_le_exp.mpr
    convert neg_le_neg he using 1 <;> ring
  calc
    _ ≤ (coverRoutingOrder xh s0 upper*v^2*t^2)*exp (-a*v^2*t) :=
      mul_le_mul hnn hexp (exp_nonneg _) (by positivity)
    _ = coverRoutingOrder xh s0 upper*(v^2*t^2*exp (-a*(v^2)*t)) := by ring
    _ ≤ coverRoutingOrder xh s0 upper*exp (-a) :=
      mul_le_mul_of_nonneg_left (two_parameter_exp_tail (one_le_pow₀ hv) ht hscale) hN.le
    _ = _ := rfl

theorem cover_bank_sampled_edges_lower {x xh s0 s lower P : ℝ}
    (hx : 0 < x) (hxxh : x ≤ xh) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 ≤ lower) (hP : lower ≤ P) :
    2*s0*(coverRoutingQ xh s0 lower)^2 ≤ 2*s*(coverRoutingQ x s P)^2 := by
  have hP0 := hlower.trans hP
  have hs := hs0.trans_le hss
  have hw := cover_w_pos hx
  have hwle := cover_w_mono hx.le hxxh
  have hwh := cover_w_pos (hx.trans_le hxxh)
  have hq0 : 0 ≤ coverRoutingQ xh s0 lower := by unfold coverRoutingQ; positivity
  have hq : coverRoutingQ xh s0 lower ≤ coverRoutingQ x s P := by
    unfold coverRoutingQ
    gcongr
  gcongr

theorem cover_bank_core_tail {x xh s0 s lower P m ε : ℝ}
    (hx : 0 < x) (hxxh : x ≤ xh) (hs0 : 0 < s0) (hss : s0 ≤ s)
    (hlower : 0 ≤ lower) (hP : lower ≤ P)
    (hm : (97/100)*(2*s*(coverRoutingQ x s P)^2) ≤ m) :
    exp (-2*ε^2*m) ≤ exp (-2*ε^2*((97/100)*(2*s0*(coverRoutingQ xh s0 lower)^2))) := by
  have hh := (mul_le_mul_of_nonneg_left
    (cover_bank_sampled_edges_lower hx hxxh hs0 hss hlower hP) (by norm_num : (0:ℝ) ≤ 97/100)).trans hm
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hh (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg ε))

end
end Cycle12
