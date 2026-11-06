import Cycle12.MarkedWitnessAssembly

namespace Cycle12
open Real
noncomputable section

theorem scaled_population_lower {nu slope a intercept z p : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hs : 0 < slope)
    (hnu : nu*slope ≤ a-intercept) :
    nu*z/p ≤ (a*z-intercept*z)/(slope*p) := by
  have hh := mul_le_mul_of_nonneg_right hnu hz.le
  apply (le_div_iff₀ (mul_pos hs hp)).mpr
  have hid : (nu*z/p)*(slope*p)=nu*slope*z := by field_simp <;> ring
  rw [hid]
  nlinarith only [hh]

theorem global_population_lower_from_cap {nu slope intercept dm beta tau cap z p : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hs : 0 < slope) (hbd : beta ≤ dm)
    (hcap : (tau-beta)/(tau+(dm-beta)/2) ≤ cap)
    (hnu : nu*slope ≤ max (dm-tau) ((1-cap)*(dm-beta))-intercept) :
    nu*z/p ≤
      (max (dm-tau) ((1-(tau-beta)/(tau+(dm-beta)/2))*(dm-beta))*z-intercept*z)/(slope*p) := by
  apply scaled_population_lower hp hz hs
  have hh := mul_le_mul_of_nonneg_right (sub_le_sub_left hcap 1) (sub_nonneg.mpr hbd)
  exact hnu.trans (sub_le_sub_right (max_le_max_left (dm-tau) hh) intercept)

theorem local_population_lower_from_cap {nu slope intercept dm beta err cap z p : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hs : 0 < slope) (hbd : beta ≤ dm)
    (hcap : (err+2*beta)/dm ≤ cap)
    (hnu : nu*slope ≤ (1-cap)*(dm-beta)-intercept) :
    nu*z/p ≤ (((1-(err+2*beta)/dm)*(dm-beta))*z-intercept*z)/(slope*p) := by
  apply scaled_population_lower hp hz hs
  exact hnu.trans (sub_le_sub_right
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hcap 1) (sub_nonneg.mpr hbd)) intercept)

/-- An interval certificate for the anchored complement population,
including the two additional units of degree charge. -/
theorem anchor_population_count_balance {n p R Rlo z Wlo dm L ew raw slope intercept : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hRlo : 0 < Rlo) (hR : Rlo ≤ R)
    (hWlo : 0 < Wlo) (hW : Wlo ≤ p*z) (hdm : 0 < dm)
    (hL : 0 ≤ L) (hew : 0 ≤ ew+2) (hitc : 0 ≤ intercept)
    (hn : p*n=z*R)
    (hbudget : slope*raw+intercept/Rlo+(ew+2)*L/(dm*Wlo) ≤ 1/2) :
    (slope*p)*(raw*n)+intercept*z ≤ (p*n)/2-(ew+2)*L*n/(dm*z) := by
  have hRp := hRlo.trans_le hR
  have hi := div_le_div_of_nonneg_left hitc hRlo hR
  have hc := div_le_div_of_nonneg_left (mul_nonneg hew hL) (mul_pos hdm hWlo)
    (mul_le_mul_of_nonneg_left hW hdm.le)
  have hb : slope*raw+intercept/R+(ew+2)*L/(dm*(p*z)) ≤ 1/2 := by
    linarith only [hi,hc,hbudget]
  have hmult := mul_le_mul_of_nonneg_right hb (mul_pos hz hRp).le
  have hni : n=z*R/p := (eq_div_iff hp.ne').mpr (by simpa only [mul_comm] using hn)
  rw [hni]
  have hid : (slope*raw+intercept/R+(ew+2)*L/(dm*(p*z)))*(z*R)=
      (slope*p)*(raw*(z*R/p))+intercept*z+(ew+2)*L*(z*R/p)/(dm*z) := by
    field_simp
    <;> ring
  rw [hid] at hmult
  have hNid : p*(z*R/p)=z*R := by field_simp
  rw [hNid]
  linarith only [hmult]

theorem anchor_first_population_lower {nu zlo z Wlo p Rlo R dm L beta raw : ℝ}
    (hp : 0 < p) (hzlo : 0 < zlo) (hz : zlo ≤ z)
    (hWlo : 0 ≤ Wlo) (hW : Wlo ≤ p*z) (hR : Rlo ≤ R)
    (hL : 0 < L) (hb : 0 ≤ beta) (hraw : 0 ≤ raw)
    (hdegree : L/zlo ≤ dm)
    (hnu1 : nu ≤ (7/8)*beta*(dm-L/zlo)*Wlo/L) (hnu2 : nu ≤ raw*Rlo) :
    nu*z/p ≤ min ((1-1/8)*((beta*z)*(dm*z-L)/L)) (raw*(z*R/p)) := by
  have hzp := hzlo.trans_le hz
  have hgap : dm-L/zlo ≤ dm-L/z := sub_le_sub_left (div_le_div_of_nonneg_left hL.le hzlo hz) dm
  have hgap0 : 0 ≤ dm-L/zlo := sub_nonneg.mpr hdegree
  have hscale : 0 ≤ (7/8:ℝ)*beta := mul_nonneg (by norm_num) hb
  have hm : (7/8)*beta*(dm-L/zlo)*Wlo/L ≤ (7/8)*beta*(dm-L/z)*(p*z)/L := by
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hgap hscale) hW hWlo
      (mul_nonneg hscale (hgap0.trans hgap))
  have hfirst := mul_le_mul_of_nonneg_right (hnu1.trans hm) (div_pos hzp hp).le
  have hsecond := mul_le_mul_of_nonneg_right
    (hnu2.trans (mul_le_mul_of_nonneg_left hR hraw)) (div_pos hzp hp).le
  apply le_min
  · convert hfirst using 1 <;> field_simp <;> ring
  · convert hsecond using 1 <;> ring

theorem anchor_second_population_lower {nu zlo z Wlo p dm L ew ce slope intercept : ℝ}
    (hnu0 : 0 ≤ nu) (hp : 0 < p) (hzlo : 0 < zlo) (hz : zlo ≤ z)
    (hWlo : 0 < Wlo) (hW : Wlo ≤ p*z) (hdm : 0 < dm)
    (hL : 0 ≤ L) (hew : 0 ≤ ew+2) (hce : 0 < ce) (hslope : 0 < slope)
    (hnu : nu*(slope+(ew+2)*L/(dm*Wlo*ce)) ≤ dm-L/zlo-intercept) :
    nu*z/p ≤ (dm*z-L-intercept*z)/(slope*p+(ew+2)*L/((dm*z)*ce)) := by
  have hzp := hzlo.trans_le hz
  have hgap := sub_le_sub_right (sub_le_sub_left (div_le_div_of_nonneg_left hL hzlo hz) dm) intercept
  have hcharge := div_le_div_of_nonneg_left (mul_nonneg hew hL) (mul_pos (mul_pos hdm hWlo) hce)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hdm.le) hce.le)
  have hbudget : nu*(slope+(ew+2)*L/(dm*(p*z)*ce)) ≤ dm-L/z-intercept := by
    exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl hcharge) hnu0).trans (hnu.trans hgap)
  have hdpos : 0 < slope*p+(ew+2)*L/((dm*z)*ce) :=
    add_pos_of_pos_of_nonneg (mul_pos hslope hp)
      (div_nonneg (mul_nonneg hew hL) (mul_pos (mul_pos hdm hzp) hce).le)
  apply (le_div_iff₀ hdpos).mpr
  have hh := mul_le_mul_of_nonneg_right hbudget hzp.le
  have hid1 : nu*(slope+(ew+2)*L/(dm*(p*z)*ce))*z=
      (nu*z/p)*(slope*p+(ew+2)*L/((dm*z)*ce)) := by field_simp <;> ring
  have hid2 : (dm-L/z-intercept)*z=dm*z-L-intercept*z := by field_simp <;> ring
  rwa [hid1,hid2] at hh

end
end Cycle12
