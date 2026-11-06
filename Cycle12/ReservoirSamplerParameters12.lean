import Cycle12.NormalizedBadCut12
import Cycle12.Foundations.BasicCertificates

namespace Cycle12
open Cycle13 Real Finset
noncomputable section

def reservoirSampleParameters : NormalizedGlobalParameters where
  dm := 45/16
  beta := 1/10
  err := 3/10
  upper := 9/8
  mark := 8
  cap := 18
  witness := 1/4
  slope := 11/10
  intercept := 1/20
  theta := 1/8
  population := 13/20
  retained := 7/8
  fraction := 4/5

theorem exp_neg_le_one_1024 {t : ℝ} (ht : 20 ≤ t) : exp (-t) ≤ 1/1024 := by
  have h5 : (6:ℝ) ≤ exp 5 := by linarith only [add_one_le_exp (5:ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 6) h5 4
  have h20 : (1296:ℝ) ≤ exp 20 := by
    rw [← exp_nat_mul] at hp
    norm_num at hp
    exact hp
  rw [exp_neg,inv_eq_one_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  have he := (exp_le_exp.mpr ht)
  linarith only [h20,he]

theorem exp_eighth_upper : exp (1/8:ℝ) ≤ 91/80 := by
  have hh := (ratExp_bounds (q := 1/8) (by norm_num) 5 (by norm_num)).2
  have hr : ratExpUpper (1/8) 5 ≤ (91/80:ℚ) := by
    norm_num [ratExpUpper,ratExpPartial,sum_range_succ,Nat.factorial]
  have hc := (Rat.cast_le (K := ℝ)).mpr hr
  push_cast at hh hc
  exact hh.trans hc

theorem reservoir_sampler_valid {p : unitInterval} {z R : ℝ}
    (hp : 0 < (p:ℝ)) (hR : 12 ≤ R) (hzR : 1048576*R ≤ z) :
    reservoirSampleParameters.Valid (p:ℝ) z R := by
  have hR0 : 0 < R := by linarith only [hR]
  have hz : 256 ≤ z := by linarith only [hR,hzR]
  have hz0 : 0 < z := by linarith only [hz]
  have hmark : 8/z ≤ 1/32 := (div_le_iff₀ hz0).mpr (by linarith only [hz])
  have hmark0 : 0 ≤ 8/z := by positivity
  have hinvR : 1/R ≤ 1/12 := (div_le_iff₀ hR0).mpr (by linarith only [hR])
  have hRz : R/z ≤ 1/1048576 := (div_le_iff₀ hz0).mpr (by linarith only [hzR])
  have hpr : 18*(p:ℝ)*R/z ≤ 18/1048576 := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul p.2.2 hRz (by positivity) (by norm_num : (0:ℝ) ≤ 1))
      (by norm_num : (0:ℝ) ≤ 18)
    convert hh using 1 <;> ring
  have he1 := exp_neg_le_one_1024 (t := 8*(45/16)) (by norm_num)
  have he2 := exp_neg_le_one_1024 (t := R*(18-(9/8)*8)^2/(2*18)) (by nlinarith only [hR])
  refine {
    p_pos := hp
    scale_pos := hz0
    ratio_lower := by linarith only [hR]
    mark_nonneg := by norm_num [reservoirSampleParameters]
    mark_lt := by dsimp [reservoirSampleParameters]; linarith only [hz]
    degree_pos := by norm_num [reservoirSampleParameters]
    expansion_lt := by norm_num [reservoirSampleParameters]
    error_pos := by norm_num [reservoirSampleParameters]
    mark_degree := by norm_num [reservoirSampleParameters]
    cap_pos := by norm_num [reservoirSampleParameters]
    mark_cap := by norm_num [reservoirSampleParameters]
    witness_pos := by norm_num [reservoirSampleParameters]
    witness_bound := ?_
    slope_pos := by norm_num [reservoirSampleParameters]
    intercept_nonneg := by norm_num [reservoirSampleParameters]
    theta_pos := by norm_num [reservoirSampleParameters]
    mgf_slope := by dsimp [reservoirSampleParameters]; linarith only [exp_eighth_upper]
    population_pos := by norm_num [reservoirSampleParameters]
    population_bound := by norm_num [reservoirSampleParameters]
    side_scale_lower := by norm_num [reservoirSampleParameters]
    retained_nonneg := by norm_num [reservoirSampleParameters]
    marked_retention := by dsimp [reservoirSampleParameters]; linarith only [hinvR,hpr]
    fraction_nonneg := by norm_num [reservoirSampleParameters]
    fraction_le_one := by norm_num [reservoirSampleParameters]
    cut_threshold := ?_ }
  · dsimp [reservoirSampleParameters]
    simp only [neg_div,neg_mul] at he1 he2 ⊢
    linarith only [he1,he2]
  · dsimp [reservoirSampleParameters]
    nlinarith only [sq_nonneg ((1-8/z)-(31/32)),hmark]

theorem reservoir_sampler_rates {p : unitInterval} {z R : ℝ}
    (hR : 12 ≤ R) (hzR : 1048576*R ≤ z) :
    2 ≤ reservoirSampleParameters.mgfRate (p:ℝ) z R ∧
    2 ≤ reservoirSampleParameters.jansonRate z R := by
  have hR0 : 0 < R := by linarith only [hR]
  have hz : 256 ≤ z := by linarith only [hR,hzR]
  have hz0 : 0 < z := by linarith only [hz]
  have hscale : 1048576 ≤ z/R := (le_div_iff₀ hR0).mpr hzR
  have hmark : 8/z ≤ 1/32 := (div_le_iff₀ hz0).mpr (by linarith only [hz])
  have hret : 31/32 ≤ 1-8/z := by linarith only [hmark]
  have hret0 : 0 < 1-8/z := by linarith only [hret]
  constructor
  · have he : exp ((1/8:ℝ)*(1-(11/10)*(p:ℝ))) ≤ 91/80 :=
      (exp_le_exp.mpr (by nlinarith only [p.2.1])).trans exp_eighth_upper
    dsimp [NormalizedGlobalParameters.mgfRate,reservoirSampleParameters]
    linarith only [hscale,he]
  · let d : ℝ := (1-8/z)*((13/20)*((45/16)-(1/10)))*z
    have hd : 1 ≤ d := by
      have hm := mul_le_mul hret (le_refl z) hz0.le hret0.le
      dsimp [d]
      nlinarith only [hm,hz]
    have hd0 : 0 < d := by linarith only [hd]
    have hinv : 1/d ≤ 1 := (div_le_one hd0).mpr hd
    have hden : 0 < 2*(2+1/d) := by positivity
    have hnum : 60 ≤ (1-(4/5:ℝ))^2*(1-8/z)*(7/8)*(z/R) := by
      have hh := mul_le_mul hret hscale (by norm_num : (0:ℝ) ≤ 1048576) hret0.le
      nlinarith only [hh]
    have hdiv : 10 ≤ ((1-(4/5:ℝ))^2*(1-8/z)*(7/8)*(z/R))/(2*(2+1/d)) :=
      (le_div_iff₀ hden).mpr (by linarith only [hinv,hnum])
    change 2 ≤ ((1-(4/5:ℝ))^2*(1-8/z)*(7/8)*(z/R))/(2*(2+1/d))-8
    linarith only [hdiv]

theorem reservoir_sampler_cut_failure {p : unitInterval} {z R : ℝ}
    (hR : 12 ≤ R) (hzR : 1048576*R ≤ z) :
    (2*exp (-R*reservoirSampleParameters.mgfRate (p:ℝ) z R)+
      exp (-R*reservoirSampleParameters.jansonRate z R))/reservoirSampleParameters.witness ≤ 1/64 := by
  obtain ⟨hm,hj⟩ := reservoir_sampler_rates (p := p) hR hzR
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hem := exp_neg_le_one_1024 (t := R*reservoirSampleParameters.mgfRate (p:ℝ) z R)
    (by nlinarith only [hR,mul_le_mul_of_nonneg_left hm hR0])
  have hej := exp_neg_le_one_1024 (t := R*reservoirSampleParameters.jansonRate z R)
    (by nlinarith only [hR,mul_le_mul_of_nonneg_left hj hR0])
  change (2*exp (-R*reservoirSampleParameters.mgfRate (p:ℝ) z R)+
      exp (-R*reservoirSampleParameters.jansonRate z R))/(1/4) ≤ 1/64
  simp only [neg_mul] at hem hej ⊢
  linarith only [hem,hej]

end
end Cycle12
