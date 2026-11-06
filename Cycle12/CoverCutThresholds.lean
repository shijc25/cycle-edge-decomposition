import Cycle12.RationalCutBin

namespace Cycle12
noncomputable section

theorem cover_cut_mass_lower {p z u residual ps tau kappa : ℝ}
    (hp : 0 < p) (hz : 0 ≤ z) (hu : 0 ≤ u) (hps : 0 ≤ ps)
    (ht : 0 ≤ tau) (hk : 0 ≤ kappa) (hres : ps*p ≤ residual) :
    (tau*kappa*ps^2)*z*p*u ≤ tau*(kappa*(z/p)*u*residual^2) := by
  have hs : (ps*p)^2 ≤ residual^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (mul_nonneg hps hp.le) hres
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ tau*(kappa*(z/p)*u) by positivity)
  have hid : (tau*(kappa*(z/p)*u))*(ps*p)^2=(tau*kappa*ps^2)*z*p*u := by
    field_simp
    <;> ring
  rw [hid] at hm
  simpa only [mul_assoc] using hm

theorem cover_counting_cut_threshold {p z u residual ps tau kappa nu slope intercept factor : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hn : 0 < nu) (hside : nu*(z/p) ≤ u)
    (hi : 0 ≤ intercept) (hf : 0 ≤ factor) (hps : 0 ≤ ps) (ht : 0 ≤ tau) (hk : 0 ≤ kappa)
    (hres : ps*p ≤ residual)
    (hbudget : factor*(slope+intercept/nu) ≤ tau*kappa*ps^2) :
    factor*z*(slope*p*u+intercept*z) ≤ tau*(kappa*(z/p)*u*residual^2) := by
  have hu : 0 ≤ u := (mul_pos hn (div_pos hz hp)).le.trans hside
  have hpop : nu*z ≤ p*u := by
    have hh := mul_le_mul_of_nonneg_left hside hp.le
    have he : p*(nu*(z/p))=nu*z := by field_simp
    rwa [he] at hh
  have hzi : intercept*z ≤ (intercept/nu)*p*u := by
    have hh := mul_le_mul_of_nonneg_left hpop (div_nonneg hi hn.le)
    have he : (intercept/nu)*(nu*z)=intercept*z := by field_simp
    rw [he] at hh
    simpa only [mul_assoc] using hh
  have hnum : slope*p*u+intercept*z ≤ (slope+intercept/nu)*p*u := by
    nlinarith only [hzi]
  have hh := mul_le_mul_of_nonneg_left hnum (mul_nonneg hf hz.le)
  have hb := mul_le_mul_of_nonneg_right hbudget (show 0 ≤ z*p*u by positivity)
  have hm := cover_cut_mass_lower hp hz.le hu hps ht hk hres
  calc
    _ ≤ factor*z*((slope+intercept/nu)*p*u) := hh
    _ = (factor*(slope+intercept/nu))*z*p*u := by ring
    _ ≤ (tau*kappa*ps^2)*z*p*u := by simpa only [mul_assoc] using hb
    _ ≤ _ := hm

theorem cover_local_cut_threshold {p z u residual ps tau kappa nu slope intercept factor cap frac : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hn : 0 < nu) (hside : nu*(z/p) ≤ u)
    (hs : 0 ≤ slope) (hi : 0 ≤ intercept) (hf : 0 ≤ factor)
    (hps : 0 ≤ ps) (ht : 0 ≤ tau) (hk : 0 ≤ kappa) (hres : ps*p ≤ residual)
    (hcap : frac ≤ cap) (hcap1 : cap < 1)
    (hbudget : factor*(slope+intercept/nu)/(1-cap) ≤ tau*kappa*ps^2) :
    factor*z*((slope*p*u+intercept*z)/(1-frac)) ≤ tau*(kappa*(z/p)*u*residual^2) := by
  have hu : 0 ≤ u := (mul_pos hn (div_pos hz hp)).le.trans hside
  have hden : 0 < 1-cap := sub_pos.mpr hcap1
  have hquot := div_le_div_of_nonneg_left (show 0 ≤ slope*p*u+intercept*z by positivity)
    hden (sub_le_sub_left hcap 1)
  have hfirst := mul_le_mul_of_nonneg_left hquot (mul_nonneg hf hz.le)
  have hmain := cover_counting_cut_threshold hp hz hn hside hi (div_nonneg hf hden.le)
    hps ht hk hres (show (factor/(1-cap))*(slope+intercept/nu) ≤ tau*kappa*ps^2 by
      simpa only [div_mul_eq_mul_div] using hbudget)
  exact hfirst.trans (by convert hmain using 1 <;> ring)

theorem cover_anchor_cut_threshold {p z u residual ps tau kappa Wlo ce factor : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hu : 0 ≤ u) (hps : 0 ≤ ps)
    (ht : 0 ≤ tau) (hk : 0 ≤ kappa) (hres : ps*p ≤ residual)
    (hW : Wlo ≤ p*z) (hce : 0 < ce)
    (hbudget : factor ≤ tau*kappa*ps^2*ce*Wlo) :
    (factor/ce)*u ≤ tau*(kappa*(z/p)*u*residual^2) := by
  have hh := mul_le_mul_of_nonneg_left hW (show 0 ≤ tau*kappa*ps^2*ce by positivity)
  have hcoef : factor/ce ≤ (tau*kappa*ps^2)*z*p := by
    apply (div_le_iff₀ hce).mpr
    nlinarith only [hbudget,hh]
  exact (mul_le_mul_of_nonneg_right hcoef hu).trans (cover_cut_mass_lower hp hz.le hu hps ht hk hres)

end
end Cycle12
