import Cycle12.JointMajorityBound

namespace Cycle12
open Real
noncomputable section

def majorityCubic (a b c x : ℝ) : ℝ := (c-x)*(a+b*(3*x-2*x^2))
def majorityCubicSlope (a b c x : ℝ) : ℝ := 3*b*c-a-2*b*(2*c+3)*x+6*b*x^2
def majorityCubicBox (a b c lo hi : ℝ) : ℝ :=
  a*c+(3*b*c-a)*(if 0 ≤ 3*b*c-a then hi else lo)-b*(2*c+3)*lo^2+2*b*hi^3

theorem majority_cubic_taylor (a b c r x : ℝ) :
    majorityCubic a b c x=majorityCubic a b c r+majorityCubicSlope a b c r*(x-r)+
      b*(x-r)^2*(2*x+4*r-(2*c+3)) := by
  unfold majorityCubic majorityCubicSlope
  ring

/-- The tangent at r<=3/4 bounds the entire unit interval, even though
the cubic need not be concave on that whole interval. -/
theorem majority_cubic_tangent_upper {a b c r x : ℝ}
    (hb : 0 ≤ b) (hc : 1 ≤ c) (hr : r ≤ 3/4) (hx : x ≤ 1) :
    majorityCubic a b c x ≤ majorityCubic a b c r+majorityCubicSlope a b c r*(x-r) := by
  rw [majority_cubic_taylor a b c r x]
  have hcoef : 2*x+4*r-(2*c+3) ≤ 0 := by linarith only [hc,hr,hx]
  have hh := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb (sq_nonneg (x-r))) hcoef
  linarith only [hh]

theorem majority_cubic_box_upper {a b c lo hi x : ℝ}
    (hb : 0 ≤ b) (hc : 1 ≤ c) (hlo : 0 ≤ lo) (hlx : lo ≤ x) (hxh : x ≤ hi) :
    majorityCubic a b c x ≤ majorityCubicBox a b c lo hi := by
  have hx0 : 0 ≤ x := hlo.trans hlx
  have hsq : lo^2 ≤ x^2 := by gcongr
  have hcube : x^3 ≤ hi^3 := by gcongr
  have hquad := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg hb (show 0 ≤ 2*c+3 by linarith only [hc]))
  have hthird := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 2*b by linarith only [hb])
  have hlinear : (3*b*c-a)*x ≤ (3*b*c-a)*(if 0 ≤ 3*b*c-a then hi else lo) := by
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left hxh h
    · exact mul_le_mul_of_nonpos_left hlx (le_of_not_ge h)
  unfold majorityCubic majorityCubicBox
  nlinarith only [hquad,hthird,hlinear]

/-- Two rational derivative signs and a rational box budget certify all
real proportions at once; no floating critical point enters the proof. -/
theorem majority_cubic_interval_bound {a b c lo hi K : ℝ}
    (hb : 0 ≤ b) (hc : 1 ≤ c) (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hhi : hi ≤ 3/4)
    (hslo : 0 ≤ majorityCubicSlope a b c lo) (hshi : majorityCubicSlope a b c hi ≤ 0)
    (hbox : majorityCubicBox a b c lo hi ≤ K) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → majorityCubic a b c x ≤ K := by
  intro x _ hx1
  by_cases hxl : x ≤ lo
  · have ht := majority_cubic_tangent_upper hb hc (hlh.trans hhi) hx1
      (a:=a) (r:=lo)
    have hm := mul_nonpos_of_nonneg_of_nonpos hslo (sub_nonpos.mpr hxl)
    have hv := majority_cubic_box_upper (a:=a) hb hc hlo le_rfl hlh
    linarith only [ht,hm,hv,hbox]
  by_cases hhx : hi ≤ x
  · have ht := majority_cubic_tangent_upper hb hc hhi hx1 (a:=a) (r:=hi)
    have hm := mul_nonpos_of_nonpos_of_nonneg hshi (sub_nonneg.mpr hhx)
    have hv := majority_cubic_box_upper (a:=a) hb hc hlo hlh le_rfl
    linarith only [ht,hm,hv,hbox]
  · exact (majority_cubic_box_upper hb hc hlo (le_of_not_ge hxl) (le_of_not_ge hhx)).trans hbox

theorem majority_cubic_zero_max {a b c : ℝ} (hb : 0 ≤ b) (hc : 1 ≤ c)
    (hs : 3*b*c ≤ a) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic a b c x ≤ a*c := by
  have hh := majority_cubic_tangent_upper (a:=a) (r:=0) hb hc (by norm_num) hx1
  simp only [majorityCubic,majorityCubicSlope] at hh
  norm_num at hh
  have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hx0
  unfold majorityCubic
  nlinarith only [hh,hm]

end
end Cycle12
