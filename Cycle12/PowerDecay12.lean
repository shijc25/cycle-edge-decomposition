import Cycle12.RenewalPotential12
import Cycle12.ScaleMassSeries

namespace Cycle12
open Real Set
noncomputable section

/-- Quantitative decay on a half-line, used for both summability and the
two-step tail payment. The rate is in base-two logarithmic units. -/
def PowerDecay (H : ℝ → ℝ) (w z : ℝ) : Prop :=
  ∀ ⦃x y : ℝ⦄,w≤x → x≤y → H y≤(2:ℝ)^(-z*(y-x))*H x

theorem PowerDecay.antitone {H : ℝ → ℝ} {w z : ℝ}
    (hd : PowerDecay H w z) (hz : 0≤z) (h0 : ∀ x,w≤x → 0≤H x) :
    AntitoneOn H (Ici w) := by
  intro x hx y hy hxy
  apply (hd hx hxy).trans
  have hp : (2:ℝ)^(-z*(y-x))≤1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) (sub_nonneg.mpr hxy)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (h0 x hx)

theorem PowerDecay.weaken {H : ℝ → ℝ} {w z t : ℝ}
    (hd : PowerDecay H w z) (ht : t≤z) (h0 : ∀ x,w≤x → 0≤H x) :
    PowerDecay H w t := by
  intro x y hx hxy
  apply (hd hx hxy).trans
  apply mul_le_mul_of_nonneg_right _ (h0 x hx)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hh := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hxy)
  linarith only [hh]

theorem PowerDecay.add {H K : ℝ → ℝ} {w z : ℝ}
    (hH : PowerDecay H w z) (hK : PowerDecay K w z) :
    PowerDecay (fun x => H x+K x) w z := by
  intro x y hx hxy
  simpa only [mul_add] using add_le_add (hH hx hxy) (hK hx hxy)

theorem PowerDecay.mul_const {H : ℝ → ℝ} {w z a : ℝ}
    (hd : PowerDecay H w z) (ha : 0≤a) : PowerDecay (fun x => a*H x) w z := by
  intro x y hx hxy
  have hh := mul_le_mul_of_nonneg_left (hd hx hxy) ha
  nlinarith only [hh]

theorem PowerDecay.mul {H K : ℝ → ℝ} {w z t : ℝ}
    (hH : PowerDecay H w z) (hK : PowerDecay K w t)
    (hH0 : ∀ x,w≤x → 0≤H x) (hK0 : ∀ x,w≤x → 0≤K x) :
    PowerDecay (fun x => H x*K x) w (z+t) := by
  intro x y hx hxy
  have hh := mul_le_mul (hH hx hxy) (hK hx hxy) (hK0 y (hx.trans hxy))
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hH0 x hx))
  apply hh.trans_eq
  calc
    _ = ((2:ℝ)^(-z*(y-x))*(2:ℝ)^(-t*(y-x)))*(H x*K x) := by ring
    _ = _ := by rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 2; ring

theorem powerDecay_power (w z : ℝ) : PowerDecay (fun x => (2:ℝ)^(-z*x)) w z := by
  intro x y hx hxy
  rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply le_of_eq
  congr 1
  ring

theorem powerDecay_linear_power {a d r t w : ℝ}
    (ha : 0≤a+d*w) (hd : 0≤d) (ht : 0≤t)
    (hslope : d≤log 2*t*(a+d*w)) :
    PowerDecay (fun x => (a+d*x)*(2:ℝ)^(-r*x)) w (r-t) := by
  intro x y hx hxy
  have hdx := mul_le_mul_of_nonneg_left hx hd
  have hax : 0≤a+d*x := by linarith only [ha,hdx]
  have hlog : 0≤log 2*t := mul_nonneg (log_pos (by norm_num)).le ht
  have hsx : d≤log 2*t*(a+d*x) :=
    hslope.trans (mul_le_mul_of_nonneg_left (by linarith only [hdx]) hlog)
  have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (log 2*t*(y-x))) hax
  have hs := mul_le_mul_of_nonneg_right hsx (sub_nonneg.mpr hxy)
  have hlin : a+d*y≤(a+d*x)*exp (log 2*t*(y-x)) := by nlinarith only [hm,hs]
  have hh := mul_le_mul_of_nonneg_right hlin (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (-r*y))
  apply hh.trans_eq
  simp only [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ = (a+d*x)*(exp (log 2*t*(y-x))*exp (log 2*(-r*y))) := by ring
    _ = (a+d*x)*exp (log 2*(-(r-t)*(y-x))+log 2*(-r*x)) := by
      rw [←Real.exp_add]; congr 2; ring
    _ = _ := by rw [Real.exp_add]; ring

theorem powerDecay_tsum {I : Type} (H : I → ℝ → ℝ) {w z : ℝ}
    (hd : ∀ i,PowerDecay (H i) w z) (hs : ∀ x,w≤x → Summable (fun i => H i x)) :
    PowerDecay (fun x => ∑' i,H i x) w z := by
  intro x y hx hxy
  rw [←tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i => hd i hx hxy)
    (hs y (hx.trans hxy)) ((hs x hx).mul_left _)

theorem powerDecay_scale_series {a w theta : ℝ}
    (ha : 0<a) (hw : 0<w) (ht : 0<theta) (ht1 : theta<1) :
    PowerDecay (fun x => scaleMassSeries theta (a*x)) w a := by
  have hp (j : ℕ) : 1≤theta⁻¹^j := one_le_pow₀ ((one_le_inv₀ ht).mpr ht1.le)
  have hd (j : ℕ) : PowerDecay (fun x => Cycle13.powerScaleTerm (a*x) theta j) w a := by
    have hh := (powerDecay_power w (a*theta⁻¹^j)).weaken
      (show a≤a*theta⁻¹^j by nlinarith only [hp j,ha])
      (fun x _ => Real.rpow_nonneg (by norm_num) _)
    convert hh using 1
    funext x
    unfold Cycle13.powerScaleTerm
    congr 1
    ring
  exact powerDecay_tsum _ hd (fun x hx => Cycle13.powerScaleSeries_summable
    (mul_pos ha (hw.trans_le hx)) ht ht1)

end
end Cycle12
