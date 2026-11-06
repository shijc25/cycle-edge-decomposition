import Mathlib

namespace Cycle12
open Real
noncomputable section

def routingRetained (a R γ : ℝ) : ℝ := 1-a-1/128-1/(R*γ)
def routingLength (n h L : ℝ) : ℕ := ⌊L*sqrt (n/h)⌋₊

theorem routing_diameter_numeric {N n h r L : ℝ}
    (hh : 0 < h) (hr : 0 < r) (hL : 1/32 < L)
    (hcoef : 8/r < (L-1/32)^2) (hN : N ≤ n) (hnh : 4096 ≤ n/h) :
    2*sqrt (2*N/(r*h))+2 < L*sqrt (n/h) := by
  have hratio : 0 < n/h := by linarith
  have hroot : 64 ≤ sqrt (n/h) := by
    apply (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt hratio.le]
    norm_num
    exact hnh
  have hc : sqrt (2/r) < (L-1/32)/2 := by
    apply (sqrt_lt' (by linarith : 0 < (L-1/32)/2)).mpr
    have heq : 8/r=4*(2/r) := by ring
    rw [heq] at hcoef
    nlinarith only [hcoef]
  have he : 2*n/(r*h)=(2/r)*(n/h) := by ring
  have hmono := sqrt_le_sqrt (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN (by norm_num : (0:ℝ) ≤ 2)) (mul_nonneg hr.le hh.le))
  rw [he,sqrt_mul (div_nonneg (by norm_num) hr.le)] at hmono
  have hstrict := mul_lt_mul_of_pos_right hc (sqrt_pos.mpr hratio)
  nlinarith only [hmono,hroot,hstrict]

theorem routing_length_pos {n h L : ℝ} (hL : 1/32 < L)
    (hnh : 4096 ≤ n/h) : 0 < routingLength n h L := by
  apply Nat.floor_pos.mpr
  have hroot : 64 ≤ sqrt (n/h) := by
    apply (sq_le_sq₀ (by norm_num) (sqrt_nonneg _)).mp
    rw [sq_sqrt (by linarith : 0 ≤ n/h)]
    norm_num
    exact hnh
  nlinarith only [hroot,hL]

theorem routing_length_le {n h L : ℝ} (hL : 0 ≤ L) :
    (routingLength n h L:ℝ) ≤ L*sqrt (n/h) := Nat.floor_le (by positivity)

theorem routing_natural_length_bound {N n h r L : ℝ} {len : ℕ}
    (hh : 0 < h) (hr : 0 < r) (hL : 1/32 < L)
    (hcoef : 8/r < (L-1/32)^2) (hN : N ≤ n) (hnh : 4096 ≤ n/h)
    (hlen : (len:ℝ) ≤ 2*sqrt (2*N/(r*h))+2) : len ≤ routingLength n h L := by
  have hLp : 0 < L := by linarith
  apply (Nat.le_floor_iff (mul_nonneg hLp.le (sqrt_nonneg (n/h)))).mpr
  exact (hlen.trans_lt (routing_diameter_numeric hh hr hL hcoef hN hnh)).le

theorem routing_capacity {n h R L B : ℝ}
    (hh : 0 < h) (hR : 0 ≤ R) (hL : 0 ≤ L) (hB : 0 ≤ B) (hn : 0 ≤ n)
    (hcube : R^2*L^2*B^2*n ≤ h^3) : R*B*routingLength n h L ≤ h := by
  have hs : (R*B*L*sqrt (n/h))^2*h=R^2*L^2*B^2*n := by
    simp only [mul_pow,sq_sqrt (div_nonneg hn hh.le)]
    field_simp <;> ring
  have hsq : (R*B*L*sqrt (n/h))^2 ≤ h^2 := by
    apply (mul_le_mul_iff_left₀ hh).mp
    nlinarith only [hs,hcube]
  have hlin : R*B*L*sqrt (n/h) ≤ h :=
    (sq_le_sq₀ (by positivity) hh.le).mp hsq
  have hl := mul_le_mul_of_nonneg_left (routing_length_le (n:=n) (h:=h) hL)
    (mul_nonneg hR hB)
  nlinarith only [hl,hlin]

theorem routing_obstacle_budget {n h B k q a x ell I f : ℝ}
    (hn : 0 ≤ n) (hq : 0 < q) (hx : 0 ≤ x) (hell : 0 ≤ ell)
    (hk : k ≤ q*B) (hI : 2*I ≤ k*n) (hf : f=x*(4*ell*I))
    (hcap : 4*B*ell*(1+q) ≤ a*h) :
    f ≤ q*a*x/(2*(1+q))*h*n := by
  have hi := mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ 2*x*ell)
  have hk' := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 2*x*ell*n)
  have hf' : f ≤ 2*x*ell*q*B*n := by nlinarith only [hi,hk',hf]
  have hm := mul_le_mul_of_nonneg_right hf' (by positivity : 0 ≤ 2*(1+q))
  have hc := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ q*x*n)
  have heq : q*a*x/(2*(1+q))*h*n=(q*a*x*h*n)/(2*(1+q)) := by ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0 < 2*(1+q))).mpr
  nlinarith only [hm,hc]

end
end Cycle12
