import Mathlib

namespace Cycle13
open Real
noncomputable section

def h128RetainedFraction : ℝ := 6/11-1/5-1/128-1/16
def h128Length (r h : ℝ) : ℕ := ⌊(32/5)*sqrt (r/h)⌋₊

theorem h128RetainedFraction_pos : 0 < h128RetainedFraction := by
  norm_num [h128RetainedFraction]

theorem h128_diameter_numeric {N r h : ℝ} (hh : 0 < h)
    (hNr : N ≤ r) (hrh : 4 ≤ r/h) :
    2*sqrt (2*N/(h128RetainedFraction*h))+2 < (32/5)*sqrt (r/h) := by
  have hratio : 0 < r/h := by linarith
  have hroot : 2 ≤ sqrt (r/h) := by
    apply (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt hratio.le]
    norm_num
    exact hrh
  have hcoeff : sqrt (2/h128RetainedFraction) < 27/10 := by
    apply (sqrt_lt' (by norm_num : (0:ℝ) < 27/10)).mpr
    norm_num [h128RetainedFraction]
  have he : 2*r/(h128RetainedFraction*h)=(2/h128RetainedFraction)*(r/h) := by ring
  have hN := sqrt_le_sqrt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNr (by norm_num : (0:ℝ) ≤ 2))
    (mul_nonneg h128RetainedFraction_pos.le hh.le))
  rw [he,sqrt_mul (div_nonneg (by norm_num) h128RetainedFraction_pos.le)] at hN
  have hs := mul_lt_mul_of_pos_right hcoeff (sqrt_pos.mpr hratio)
  nlinarith only [hN,hroot,hs]

theorem h128_length_pos {r h : ℝ} (hrh : 4 ≤ r/h) : 0 < h128Length r h := by
  apply Nat.floor_pos.mpr
  have hh : 2 ≤ sqrt (r/h) := by
    apply (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt (by linarith : 0 ≤ r/h)]
    norm_num
    exact hrh
  linarith

theorem h128_length_le {r h : ℝ} :
    (h128Length r h:ℝ) ≤ (32/5)*sqrt (r/h) :=
  Nat.floor_le (by positivity)

theorem h128_capacity {r h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hcube : 16384*B^2*r ≤ h^3) : 20*B*h128Length r h ≤ h := by
  have hs : (128*B*sqrt (r/h))^2*h=16384*B^2*r := by
    rw [mul_pow,mul_pow,sq_sqrt (div_nonneg hr hh.le)]
    field_simp
    ring
  have hsq : (128*B*sqrt (r/h))^2 ≤ h^2 := by
    apply (mul_le_mul_iff_left₀ hh).mp
    nlinarith only [hs,hcube]
  have hlinear : 128*B*sqrt (r/h) ≤ h :=
    (sq_le_sq₀ (by positivity) hh.le).mp hsq
  have hl := mul_le_mul_of_nonneg_left (h128_length_le (r:=r) (h:=h))
    (by positivity : 0 ≤ 20*B)
  nlinarith only [hl,hlinear]

theorem h128_natural_length_bound {N r h : ℝ} {n : ℕ}
    (hh : 0 < h) (hNr : N ≤ r) (hrh : 4 ≤ r/h)
    (hn : (n:ℝ) ≤ 2*sqrt (2*N/(h128RetainedFraction*h))+2) :
    n ≤ h128Length r h := by
  apply (Nat.le_floor_iff (by positivity : (0:ℝ) ≤ (32/5)*sqrt (r/h))).mpr
  exact (hn.trans_lt (h128_diameter_numeric hh hNr hrh)).le

end
end Cycle13
