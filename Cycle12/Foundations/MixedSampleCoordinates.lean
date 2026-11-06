import Cycle12.Foundations.ScaleTailBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Cycle13.MixedSample
open Real
noncomputable section
set_option backward.isDefEq.respectTransparency false

def xmax : ℝ := 219/5000
def w (x : ℝ) : ℝ := 216*x^2
def v (x : ℝ) : ℝ := w x*(1+2*x)
def a (x : ℝ) : ℝ := 49/100+(11/100)*v x+(7/100)*(v x)^2
def P (x : ℝ) : ℝ := (1+2*x)*a x
def p (x : ℝ) : ℝ := w x*P x
def H (x : ℝ) : ℝ := 103/250+(117/100)*x
def denom (x : ℝ) : ℝ := 1-(33/125)*w x
def z (x : ℝ) : ℝ := 432*P x*H x/(w x*denom x)
def R (x : ℝ) : ℝ := 2*denom x/(H x*w x)
def D (x : ℝ) : ℝ := 216*P x*(H x)^2/(denom x)^2
/-- The regular extension at zero; `p(x)*z(x)` agrees for positive x. -/
def W (x : ℝ) : ℝ := 432*(P x)^2*H x/denom x
def order (x : ℝ) : ℝ := 864/(w x)^3
def sampleOrder (x : ℝ) : ℝ := 864*P x/(w x)^2
def mu (x : ℝ) : ℝ := (1+(149/50)*x)/H x

theorem w_nonneg (x : ℝ) : 0 ≤ w x := by unfold w; positivity
theorem w_pos {x : ℝ} (hx : 0 < x) : 0 < w x := by unfold w; positivity
theorem w_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : w x ≤ w y :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy 2) (by norm_num)

theorem v_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ v x :=
  mul_nonneg (w_nonneg x) (by linarith)

theorem v_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : v x ≤ v y :=
  mul_le_mul (w_mono hx hxy) (by linarith) (by linarith) (w_nonneg y)

theorem a_lower {x : ℝ} (hx : 0 ≤ x) : (49/100:ℝ) ≤ a x := by
  unfold a
  nlinarith [v_nonneg hx,sq_nonneg (v x)]

theorem a_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : a x ≤ a y := by
  have hv := v_mono hx hxy
  have hv2 := pow_le_pow_left₀ (v_nonneg hx) hv 2
  unfold a
  linarith

theorem P_lower {x : ℝ} (hx : 0 ≤ x) : (49/100:ℝ) ≤ P x := by
  have ha := a_lower hx
  have hmul := mul_nonneg hx (show 0 ≤ a x by linarith)
  unfold P
  nlinarith

theorem P_pos {x : ℝ} (hx : 0 ≤ x) : 0 < P x := lt_of_lt_of_le (by norm_num) (P_lower hx)

theorem P_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : P x ≤ P y := by
  unfold P
  exact mul_le_mul (by linarith) (a_mono hx hxy)
    (by linarith [a_lower hx]) (by linarith)

theorem p_pos {x : ℝ} (hx : 0 < x) : 0 < p x := mul_pos (w_pos hx) (P_pos hx.le)

theorem p_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : p x ≤ p y :=
  mul_le_mul (w_mono hx hxy) (P_mono hx hxy) (P_pos hx).le (w_nonneg y)

theorem H_pos {x : ℝ} (hx : 0 ≤ x) : 0 < H x := by unfold H; positivity
theorem H_mono {x y : ℝ} (hxy : x ≤ y) : H x ≤ H y := by unfold H; linarith

theorem denom_pos {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ xmax) : 0 < denom x := by
  have hw := w_mono hx hxmax
  norm_num [w,xmax] at hw
  unfold denom w
  linarith

theorem denom_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : denom y ≤ denom x := by
  have hw := w_mono hx hxy
  unfold denom
  linarith

theorem z_pos {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : 0 < z x := by
  exact div_pos (mul_pos (mul_pos (by norm_num) (P_pos hx.le)) (H_pos hx.le))
    (mul_pos (w_pos hx) (denom_pos hx.le hxmax))

theorem R_pos {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : 0 < R x := by
  exact div_pos (mul_pos (by norm_num) (denom_pos hx.le hxmax)) (mul_pos (H_pos hx.le) (w_pos hx))

theorem R_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hymax : y ≤ xmax) : R y ≤ R x := by
  have hy : 0 < y := hx.trans_le hxy
  unfold R
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (denom_antitone hx.le hxy)
    (by norm_num : (0:ℝ) ≤ 2)) (mul_pos (H_pos hy.le) (w_pos hy)).le).trans
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (denom_pos hx.le (hxy.trans hymax)).le)
    (mul_pos (H_pos hx.le) (w_pos hx))
    (mul_le_mul (H_mono hxy) (w_mono hx.le hxy) (w_nonneg x) (H_pos hy.le).le)

theorem D_pos {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ xmax) : 0 < D x := by
  exact div_pos (mul_pos (mul_pos (by norm_num) (P_pos hx)) (sq_pos_of_pos (H_pos hx)))
    (sq_pos_of_pos (denom_pos hx hxmax))

theorem D_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hymax : y ≤ xmax) : D x ≤ D y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hn := mul_le_mul (mul_le_mul_of_nonneg_left (P_mono hx hxy) (by norm_num : (0:ℝ) ≤ 216))
    (pow_le_pow_left₀ (H_pos hx).le (H_mono hxy) 2) (sq_nonneg (H x))
    (mul_pos (by norm_num) (P_pos hy)).le
  have hd := pow_le_pow_left₀ (denom_pos hy hymax).le (denom_antitone hx hxy) 2
  unfold D
  exact (div_le_div_of_nonneg_right hn (sq_nonneg (denom x))).trans
    (div_le_div_of_nonneg_left (by positivity [P_pos hy]) (sq_pos_of_pos (denom_pos hy hymax)) hd)

theorem ratio_identity {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : z x/R x=D x := by
  have hw := w_pos hx
  have hh := H_pos hx.le
  have hd := denom_pos hx.le hxmax
  unfold z R D
  field_simp <;> ring

theorem order_identity {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : R x*z x/p x=order x := by
  have hw := w_pos hx
  have hh := H_pos hx.le
  have hd := denom_pos hx.le hxmax
  have hp := P_pos hx.le
  unfold z R p order
  field_simp <;> ring

theorem sampleOrder_identity (x : ℝ) : p x*order x=sampleOrder x := by
  by_cases hw : w x=0
  · simp [p,order,sampleOrder,hw]
  · unfold p order sampleOrder
    field_simp <;> ring

def vDeriv (x : ℝ) : ℝ := 432*x*(1+3*x)
def PDeriv (x : ℝ) : ℝ := 2*a x+(1+2*x)*(11/100+(14/100)*v x)*vDeriv x

theorem hasDerivAt_w (x : ℝ) : HasDerivAt w (432*x) x := by
  convert! HasDerivAt.const_mul (216:ℝ) ((hasDerivAt_id x).pow 2) using 1 <;>
    simp [w,Pi.pow_apply] <;> ring

theorem hasDerivAt_v (x : ℝ) : HasDerivAt v (vDeriv x) x := by
  convert! (hasDerivAt_w x).mul (HasDerivAt.const_add (1:ℝ)
    (HasDerivAt.const_mul (2:ℝ) (hasDerivAt_id x))) using 1 <;>
    simp [v,vDeriv,w] <;> ring

theorem hasDerivAt_a (x : ℝ) : HasDerivAt a ((11/100+(14/100)*v x)*vDeriv x) x := by
  convert! (HasDerivAt.const_add (49/100:ℝ) (HasDerivAt.const_mul (11/100:ℝ) (hasDerivAt_v x))).add
    (HasDerivAt.const_mul (7/100:ℝ) ((hasDerivAt_v x).pow 2)) using 1 <;> simp [a] <;> ring

theorem hasDerivAt_P (x : ℝ) : HasDerivAt P (PDeriv x) x := by
  convert! (HasDerivAt.const_add (1:ℝ) (HasDerivAt.const_mul (2:ℝ) (hasDerivAt_id x))).mul
    (hasDerivAt_a x) using 1 <;> simp [P,PDeriv] <;> ring

theorem hasDerivAt_H (x : ℝ) : HasDerivAt H (117/100) x := by
  convert! HasDerivAt.const_add (103/250:ℝ) (HasDerivAt.const_mul (117/100:ℝ) (hasDerivAt_id x)) using 1 <;>
    simp [H]

theorem hasDerivAt_denom (x : ℝ) : HasDerivAt denom (-(33/125)*(432*x)) x := by
  convert! HasDerivAt.const_sub (1:ℝ) (HasDerivAt.const_mul (33/125:ℝ) (hasDerivAt_w x)) using 1 <;>
    simp [denom] <;> ring

theorem PDeriv_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ PDeriv x := by
  have ha : 0 ≤ a x := by linarith [a_lower hx]
  have hv := v_nonneg hx
  unfold PDeriv vDeriv
  positivity

theorem PDeriv_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : PDeriv x ≤ PDeriv y := by
  have ha := a_mono hx hxy
  have hv := v_mono hx hxy
  have hv0 := v_nonneg hx
  have hy : 0 ≤ y := hx.trans hxy
  have hvy := v_nonneg hy
  unfold PDeriv vDeriv
  gcongr <;> first | positivity | linarith

theorem P_deriv_budget {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ xmax) :
    2*x*PDeriv x ≤ P x := by
  have hb := mul_le_mul hxmax (PDeriv_mono hx hxmax) (PDeriv_nonneg hx)
    (by norm_num [xmax] : 0 ≤ xmax)
  have he : xmax*PDeriv xmax ≤ (49/200:ℝ) := by norm_num [PDeriv,vDeriv,xmax,a,v,w]
  nlinarith [P_lower hx]

theorem H_deriv_budget {x : ℝ} (hxmax : x ≤ xmax) : 8*x*(117/100) ≤ H x := by
  unfold H
  norm_num [xmax] at hxmax
  linarith

theorem denom_deriv_budget {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ xmax) :
    4*((33/125)*x*(432*x)) ≤ denom x := by
  have hw := w_mono hx hxmax
  norm_num [w,xmax] at hw
  unfold denom w
  nlinarith

def scaledZ (x : ℝ) : ℝ := 2*P x*H x/(x*denom x)
def scaledZDeriv (x : ℝ) : ℝ :=
  2*((PDeriv x*H x+P x*(117/100))*(x*denom x)-
    P x*H x*(denom x-(33/125)*x*(432*x)))/(x*denom x)^2

theorem scaledZ_eq {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : scaledZ x=x*z x := by
  have hd := denom_pos hx.le hxmax
  unfold scaledZ z w
  field_simp <;> ring

theorem hasDerivAt_scaledZ {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) :
    HasDerivAt scaledZ (scaledZDeriv x) x := by
  have hd := denom_pos hx.le hxmax
  have hN := HasDerivAt.const_mul (2:ℝ) ((hasDerivAt_P x).mul (hasDerivAt_H x))
  have hden := (hasDerivAt_id x).mul (hasDerivAt_denom x)
  convert! hN.div hden (mul_pos hx hd).ne' using 1 <;>
    first | (funext y; simp [scaledZ]; ring) | (simp [scaledZDeriv]; ring)

theorem scaledZDeriv_nonpos {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : scaledZDeriv x ≤ 0 := by
  have hp := P_pos hx.le
  have hh := H_pos hx.le
  have hd := denom_pos hx.le hxmax
  have h₁ := mul_le_mul_of_nonneg_right (P_deriv_budget hx.le hxmax) (mul_pos hh hd).le
  have h₂ := mul_le_mul_of_nonneg_right (H_deriv_budget hxmax) (mul_pos hp hd).le
  have h₃ := mul_le_mul_of_nonneg_right (denom_deriv_budget hx.le hxmax) (mul_pos hp hh).le
  have hnum : (PDeriv x*H x+P x*(117/100))*(x*denom x)-
      P x*H x*(denom x-(33/125)*x*(432*x)) ≤ 0 := by
    nlinarith [mul_pos (mul_pos hp hh) hd]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hnum) (sq_nonneg _)

theorem scaledZ_antitone : AntitoneOn scaledZ (Set.Ioc 0 xmax) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=scaledZDeriv) (convex_Ioc 0 xmax)
  · intro x hx
    exact (hasDerivAt_scaledZ hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (hasDerivAt_scaledZ hx'.1 hx'.2).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact scaledZDeriv_nonpos hx'.1 hx'.2

/-- A stronger elementary bound than the exponent 2/3 used in the paper's
elasticity estimate: the product x*z(x) is already decreasing. -/
theorem z_inverse_scale {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hymax : y ≤ xmax) :
    z y*(y/x) ≤ z x := by
  have hm := scaledZ_antitone ⟨hx,hxy.trans hymax⟩ ⟨hx.trans_le hxy,hymax⟩ hxy
  rw [scaledZ_eq (hx.trans_le hxy) hymax,scaledZ_eq hx (hxy.trans hymax)] at hm
  have he : z y*(y/x)=(y*z y)/x := by ring
  rw [he]
  exact (div_le_iff₀ hx).mpr (by nlinarith)

theorem z_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hymax : y ≤ xmax) : z y ≤ z x := by
  have hr : 1 ≤ y/x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  have hm := mul_le_mul_of_nonneg_left hr (z_pos (hx.trans_le hxy) hymax).le
  have hh : z y ≤ z y*(y/x) := by simpa using hm
  exact hh.trans (z_inverse_scale hx hxy hymax)

theorem p_lt_one {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ xmax) : p x < 1 := by
  exact (p_mono hx hxmax).trans_lt (by norm_num [p,w,P,a,v,xmax])

theorem R_lower {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : (9:ℝ) ≤ R x := by
  exact (by norm_num [R,denom,w,H,xmax] : (9:ℝ) ≤ R xmax).trans (R_antitone hx hxmax le_rfl)

theorem W_identity {x : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) : W x=p x*z x := by
  have hw := w_pos hx
  have hd := denom_pos hx.le hxmax
  unfold W p z
  field_simp <;> ring

theorem W_pos {x : ℝ} (hx : 0 ≤ x) (hxmax : x ≤ xmax) : 0 < W x := by
  exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (P_pos hx))) (H_pos hx))
    (denom_pos hx hxmax)

theorem W_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hymax : y ≤ xmax) : W x ≤ W y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hn := mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (P_pos hx).le (P_mono hx hxy) 2)
      (by norm_num : (0:ℝ) ≤ 432)) (H_mono hxy) (H_pos hx).le (by positivity : 0 ≤ 432*(P y)^2)
  unfold W
  exact (div_le_div_of_nonneg_right hn (denom_pos hx (hxy.trans hymax)).le).trans
    (div_le_div_of_nonneg_left (by positivity [H_pos hy]) (denom_pos hy hymax) (denom_antitone hx hxy))

theorem mu_pos {x : ℝ} (hx : 0 ≤ x) : 0 < mu x := div_pos (by positivity) (H_pos hx)

theorem mu_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : mu x ≤ mu y := by
  have hy : 0 ≤ y := hx.trans hxy
  unfold mu
  apply (div_le_div_iff₀ (H_pos hx) (H_pos hy)).mpr
  unfold H
  nlinarith

theorem sampleOrder_ratio {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    sampleOrder x ≤ sampleOrder y*(y/x)^4 := by
  have hy : 0 < y := hx.trans_le hxy
  have he : sampleOrder y*(y/x)^4=864*P y/(w x)^2 := by
    unfold sampleOrder w
    field_simp <;> ring
  rw [he]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (P_mono hx.le hxy) (by norm_num)) (sq_nonneg _)

theorem order_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : order x=order y*(y/x)^6 := by
  unfold order w
  field_simp <;> ring

theorem degree_tail_at_zero {x y rate : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hymax : y ≤ xmax)
    (hrate : (6:ℝ) ≤ rate*z y) :
    order x*exp (-rate*z x) ≤ order y*exp (-rate*z y) := by
  have hy : 0 < y := hx.trans_le hxy
  have hzy := z_pos hy hymax
  have hrp : 0 ≤ rate := by nlinarith
  have hratio : 1 ≤ y/x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  have hz := z_inverse_scale hx hxy hymax
  have hexp : exp (-rate*z x) ≤ exp (-(rate*z y)*(y/x)) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hz hrp]
  have hn : 0 ≤ order y := by unfold order; positivity [w_pos hy]
  rw [order_ratio hx hy]
  calc
    _ ≤ order y*((y/x)^6*exp (-(rate*z y)*(y/x))) := by
      have hh := mul_le_mul_of_nonneg_left hexp (mul_nonneg hn (pow_nonneg (by linarith : 0 ≤ y/x) 6))
      convert hh using 1 <;> ring
    _ ≤ _ := by simpa only [neg_mul] using mul_le_mul_of_nonneg_left (polynomial_exp_tail_scale hratio hrate) hn

def PoverX (x : ℝ) : ℝ := P x/x
def PoverXDeriv (x : ℝ) : ℝ := (PDeriv x*x-P x)/x^2

theorem hasDerivAt_PoverX {x : ℝ} (hx : 0 < x) : HasDerivAt PoverX (PoverXDeriv x) x := by
  convert! (hasDerivAt_P x).div (hasDerivAt_id x) hx.ne' using 1 <;>
    first | (funext y; simp [PoverX]) | (simp [PoverXDeriv] <;> ring)

theorem PoverX_antitone : AntitoneOn PoverX (Set.Ioc 0 xmax) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=PoverXDeriv) (convex_Ioc 0 xmax)
  · intro x hx
    exact (hasDerivAt_PoverX hx.1).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_PoverX (interior_subset hx).1).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have hb := P_deriv_budget hx'.1.le hx'.2
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [P_pos hx'.1.le]) (sq_nonneg x)

theorem sampleOrder_factor {x : ℝ} (hx : 0 < x) : sampleOrder x=(1/54:ℝ)*(PoverX x/x^3) := by
  unfold sampleOrder w PoverX
  field_simp <;> ring

theorem sampleOrder_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hymax : y ≤ xmax) :
    sampleOrder y ≤ sampleOrder x := by
  have hy : 0 < y := hx.trans_le hxy
  have hp := PoverX_antitone ⟨hx,hxy.trans hymax⟩ ⟨hy,hymax⟩ hxy
  have hx3 := pow_pos hx 3
  have hy3 := pow_pos hy 3
  rw [sampleOrder_factor hy,sampleOrder_factor hx]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/54)
  exact (div_le_div_of_nonneg_right hp hy3.le).trans
    (div_le_div_of_nonneg_left (div_pos (P_pos hx.le) hx).le hx3 (pow_le_pow_left₀ hx.le hxy 3))

theorem interval_coordinates {lo x hi s₀ s : ℝ}
    (hlo : 0 ≤ lo) (hx : 0 < x) (hlx : lo ≤ x) (hxh : x ≤ hi) (hhi : hi ≤ xmax)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) :
    p lo ≤ p x ∧ p x ≤ p hi ∧ s₀*z hi ≤ s*z x ∧ s₀*R hi ≤ s*R x ∧
      D lo ≤ (s*z x)/(s*R x) := by
  have hsp : 0 < s := hs₀.trans_le hs
  have hhip : 0 < hi := hx.trans_le hxh
  refine ⟨p_mono hlo hlx,p_mono hx.le hxh,
    mul_le_mul hs (z_antitone hx hxh hhi) (z_pos hhip hhi).le hsp.le,
    mul_le_mul hs (R_antitone hx hxh hhi) (R_pos hhip hhi).le hsp.le,?_⟩
  rw [mul_div_mul_left _ _ hsp.ne',ratio_identity hx (hxh.trans hhi)]
  exact D_mono hlo hlx (hxh.trans hhi)

theorem scaled_order_identity {x s : ℝ} (hx : 0 < x) (hxmax : x ≤ xmax) :
    (s*R x)*(s*z x)/p x=s^2*order x := by
  calc
    _ = s^2*(R x*z x/p x) := by ring
    _ = _ := by rw [order_identity hx hxmax]

theorem sampleOrder_pos {x : ℝ} (hx : 0 < x) : 0 < sampleOrder x :=
  div_pos (mul_pos (by norm_num) (P_pos hx.le)) (sq_pos_of_pos (w_pos hx))

theorem sharp_cut_failure_on_rectangle {n : ℕ} {x y s₀ s upper dm ε lam L : ℝ}
    (hn : 0 < n) (hx : 0 < x) (hxy : x ≤ y) (hymax : y ≤ xmax)
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hupper : 0 < upper) (hdm : 0 ≤ dm)
    (horder : (n:ℝ) ≤ upper*s^2*sampleOrder x)
    (hlog : log (upper*s₀^2*sampleOrder y) ≤ L) (hL : (4:ℝ) ≤ L)
    (hgap : 0 < 2*ε^2*dm*s₀*z y-2*L) (hlam : dm*s*z x ≤ lam) :
    0 < 2*ε^2*lam-2*log (n:ℝ) ∧
      sharpCutFailure n ε lam ≤
        (2*ε^2*dm*s₀*z y)/(2*ε^2*dm*s₀*z y-2*L)*exp (-(2*ε^2*dm*s₀*z y-2*L)) := by
  have hy : 0 < y := hx.trans_le hxy
  have hsp : 0 < s := hs₀.trans_le hs
  let u := y/x
  let t := s/s₀
  let N := upper*s₀^2*sampleOrder y
  have hu : 1 ≤ u := (le_div_iff₀ hx).mpr (by simpa using hxy)
  have ht : 1 ≤ t := (le_div_iff₀ hs₀).mpr (by simpa using hs)
  have hN : 0 < N := mul_pos (mul_pos hupper (sq_pos_of_pos hs₀)) (sampleOrder_pos hy)
  have hn' : (n:ℝ) ≤ N*u^4*t^2 := by
    apply horder.trans
    calc
      _ ≤ (upper*s^2)*(sampleOrder y*(y/x)^4) :=
        mul_le_mul_of_nonneg_left (sampleOrder_ratio hx hxy) (mul_nonneg hupper.le (sq_nonneg s))
      _ = _ := by dsimp [N,u,t]; field_simp <;> ring
  have hA : (2*ε^2*dm*s₀*z y)*(u*t) ≤ 2*ε^2*lam := by
    calc
      _ = (2*ε^2)*(dm*s*(z y*(y/x))) := by dsimp [u,t]; field_simp <;> ring
      _ ≤ (2*ε^2)*(dm*s*z x) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (z_inverse_scale hx hxy hymax) (mul_nonneg hdm hsp.le)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlam (by positivity)
  exact sharp_cut_failure_two_scale hn hN hu ht hn' hlog hL (by norm_num; linarith) hgap hA

end
end Cycle13.MixedSample
