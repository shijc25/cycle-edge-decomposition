import Cycle12.ReservoirScaleEndpoints12
import Cycle12.GlobalBankPreparation12
import Cycle12.ThreeReservoirSampling12

namespace Cycle12.Global12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem reservoir_linear_halfline {w : ℝ} (hw : w0 ≤ w) :
    (2:ℝ)^60*w ≤ (2:ℝ)^(s*w) := by
  have he : (2:ℝ)^(70:ℝ) ≤ (2:ℝ)^(s*w0) :=
    rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [s,w0])
  have hb : (0:ℝ)+(2:ℝ)^60*w0 ≤ (2:ℝ)^(s*w0) :=
    (show (0:ℝ)+(2:ℝ)^60*w0 ≤ (2:ℝ)^(70:ℝ) by norm_num [w0]).trans he
  have hs : (2:ℝ)^60 ≤ log 2*s*(0+(2:ℝ)^60*w0) := by
    have hl := log_two_lower
    norm_num [s,w0]
    nlinarith only [hl]
  simpa only [zero_add] using linear_power_envelope (by norm_num [w0]) hb hs hw

theorem reservoir_degree_gates {w n k : ℝ} (hw : w0 ≤ w) (hk : 1/2048 ≤ k)
    (hn : 0 < n) (horder : n ≤ (2:ℝ)^(rho*w)) :
    8192 ≤ p*k*(2:ℝ)^(s*w) ∧
    8192*log n ≤ p*k*(2:ℝ)^(s*w) ∧
    3072*log n ≤ p*k*(2:ℝ)^(s*w) := by
  have hw1 : 1 ≤ w := (show (1:ℝ) ≤ w0 by norm_num [w0]).trans hw
  have hk0 : 0 < k := by linarith only [hk]
  have hp0 : 0 < p := by norm_num [p]
  have hpk : (1/134217728:ℝ) ≤ p*k := by
    have hh := mul_le_mul (show (1/65536:ℝ) ≤ p by norm_num [p]) hk
      (by norm_num : (0:ℝ) ≤ 1/2048) hp0.le
    norm_num at hh
    exact hh
  have hlin := reservoir_linear_halfline hw
  have hm := mul_le_mul hpk hlin (by positivity : (0:ℝ) ≤ (2:ℝ)^60*w) (mul_pos hp0 hk0).le
  norm_num only [pow_succ,pow_zero,one_mul] at hm
  have hlog := log_le_log hn horder
  rw [log_rpow (by norm_num : (0:ℝ)<2)] at hlog
  have hl : log 2 ≤ 1 := by have hh := Cycle13.log_two_24_digits.2; linarith only [hh]
  have hcoef : 0 ≤ rho*w := mul_nonneg (by norm_num [rho]) (by linarith only [hw1])
  have hlog2 := mul_le_mul_of_nonneg_left hl hcoef
  have hr : rho*w ≤ 2*w := mul_le_mul_of_nonneg_right (by norm_num [rho] : rho ≤ 2)
    (by linarith only [hw1])
  constructor
  · nlinarith only [hm,hw1]
  constructor <;> nlinarith only [hm,hlog,hlog2,hr,hw1]

theorem reservoir_capacity_halfline {start w k n : ℝ} (hw : start ≤ w) (hk : 0 < k)
    (hbase : 2112/(p^2*k^2) ≤ (2:ℝ)^((2*s-rho)*start))
    (horder : n ≤ (2:ℝ)^(rho*w)) :
    2112*n ≤ (p*k*(2:ℝ)^(s*w))^2 ∧
    9437184*n ≤ p*(k*(2:ℝ)^(s*w))^2 := by
  have hp : 0 < p := by norm_num [p]
  have hcoeff : 0 < p^2*k^2 := mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos hk)
  have hpow := hbase.trans (rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left hw (by norm_num [s,rho] : 0 ≤ 2*s-rho)))
  have hb : 2112 ≤ (2:ℝ)^((2*s-rho)*w)*(p^2*k^2) := (div_le_iff₀ hcoeff).mp hpow
  have hm := mul_le_mul_of_nonneg_right hb (rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (rho*w))
  have hid : ((2:ℝ)^((2*s-rho)*w)*(p^2*k^2))*(2:ℝ)^(rho*w) =
      (p*k*(2:ℝ)^(s*w))^2 := by
    calc
      _ = (p^2*k^2)*((2:ℝ)^((2*s-rho)*w)*(2:ℝ)^(rho*w)) := by ring
      _ = (p^2*k^2)*(2:ℝ)^((s*w)*2) := by rw [← rpow_add (by norm_num : (0:ℝ)<2)]; congr 2; ring
      _ = _ := by
        have he := rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) (s*w) 2
        norm_num only [Nat.cast_ofNat] at he
        rw [he]
        ring
  rw [hid] at hm
  have hsq : 2112*n ≤ (p*k*(2:ℝ)^(s*w))^2 :=
    (mul_le_mul_of_nonneg_left horder (by norm_num : (0:ℝ) ≤ 2112)).trans hm
  refine ⟨hsq,?_⟩
  by_cases hn : 0 ≤ n
  · have hscale : 9437184*p ≤ (2112:ℝ) := by norm_num [p]
    have hb := (mul_le_mul_of_nonneg_right hscale hn).trans hsq
    have he : p*(9437184*n) ≤ p*(p*(k*(2:ℝ)^(s*w))^2) := by nlinarith only [hb]
    nlinarith only [he,hp]
  · exact (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith only [hn])).trans (by positivity)

theorem balanced_reservoir_scale_gates {w n : ℝ} (hw : w0 ≤ w) (hn : 0 < n)
    (horder : n ≤ (2:ℝ)^(rho*w)) :
    8192 ≤ p*comparison_bank*(2:ℝ)^(s*w) ∧
    8192*log n ≤ p*comparison_bank*(2:ℝ)^(s*w) ∧
    3072*log n ≤ p*comparison_bank*(2:ℝ)^(s*w) ∧
    2112*n ≤ (p*comparison_bank*(2:ℝ)^(s*w))^2 ∧
    9437184*n ≤ p*(comparison_bank*(2:ℝ)^(s*w))^2 := by
  obtain ⟨ha,hb,hc⟩ := reservoir_degree_gates (k := comparison_bank) hw (by norm_num [comparison_bank]) hn horder
  obtain ⟨hd,he⟩ := reservoir_capacity_halfline (k := comparison_bank) hw (by norm_num [comparison_bank]) balanced_capacity_base horder
  exact ⟨ha,hb,hc,hd,he⟩

theorem completion_reservoir_scale_gates {w n : ℝ} (hw : wA ≤ w) (hn : 0 < n)
    (horder : n ≤ (2:ℝ)^(rho*w)) :
    8192 ≤ p*completion_bank*(2:ℝ)^(s*w) ∧
    8192*log n ≤ p*completion_bank*(2:ℝ)^(s*w) ∧
    3072*log n ≤ p*completion_bank*(2:ℝ)^(s*w) ∧
    2112*n ≤ (p*completion_bank*(2:ℝ)^(s*w))^2 ∧
    9437184*n ≤ p*(completion_bank*(2:ℝ)^(s*w))^2 := by
  have hw0 : w0 ≤ w := (show w0 ≤ wA by norm_num [w0,wA]).trans hw
  obtain ⟨ha,hb,hc⟩ := reservoir_degree_gates (k := completion_bank) hw0 (by norm_num [completion_bank]) hn horder
  obtain ⟨hd,he⟩ := reservoir_capacity_halfline (k := completion_bank) hw (by norm_num [completion_bank]) completion_capacity_base horder
  exact ⟨ha,hb,hc,hd,he⟩

end
end Cycle12.Global12
