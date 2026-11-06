import Cycle12.Foundations.SharpAllCuts

namespace Cycle13
open Real
noncomputable section

theorem polynomial_exp_tail_scale {s a : ℝ} {k : ℕ}
    (hs : 1 ≤ s) (ha : (k:ℝ) ≤ a) :
    s^k*exp (-a*s) ≤ exp (-a) := by
  have hs0 : 0 < s := by linarith
  have hlog := log_le_sub_one_of_pos hs0
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) k)
  have ha' := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hs)
  calc
    _ = exp ((k:ℝ)*log s-a*s) := by rw [sub_eq_add_neg,exp_add,exp_nat_mul,exp_log hs0]; ring
    _ ≤ _ := exp_le_exp.mpr (by linarith)

theorem two_parameter_exp_tail {y t a : ℝ} (hy : 1 ≤ y) (ht : 1 ≤ t) (ha : 2 ≤ a) :
    y*t^2*exp (-a*y*t) ≤ exp (-a) := by
  have hys : y ≤ y^2 := by nlinarith
  have hcoeff : y*t^2 ≤ (y*t)^2 := by nlinarith [mul_le_mul_of_nonneg_right hys (sq_nonneg t)]
  have he : -a*y*t= -a*(y*t) := by ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right hcoeff (exp_nonneg _)).trans
    (polynomial_exp_tail_scale (by nlinarith : 1 ≤ y*t) (by exact_mod_cast ha : (2:ℝ) ≤ a))

theorem log_two_scale_bound {N u t L : ℝ} {k j : ℕ}
    (hN : 0 < N) (hu : 1 ≤ u) (ht : 1 ≤ t)
    (hlog : log N ≤ L) (hk : (k:ℝ) ≤ L) (hj : (j:ℝ) ≤ L) :
    log (N*u^k*t^j) ≤ L*(u*t) := by
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < t := by linarith
  have hL : 0 ≤ L := (Nat.cast_nonneg k).trans hk
  rw [log_mul (mul_pos hN (pow_pos hu0 _)).ne' (pow_pos ht0 _).ne',
    log_mul hN.ne' (pow_pos hu0 _).ne',log_pow,log_pow]
  have huLog := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hu0) (Nat.cast_nonneg (α:=ℝ) k)
  have htLog := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos ht0) (Nat.cast_nonneg (α:=ℝ) j)
  have hku := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hu)
  have hjt := mul_le_mul_of_nonneg_right hj (sub_nonneg.mpr ht)
  have hprod : 0 ≤ L*((u-1)*(t-1)) := mul_nonneg hL (mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr ht))
  nlinarith

theorem sharp_failure_scale_bound {A A₀ ell L s : ℝ}
    (hs : 1 ≤ s) (hL : 0 ≤ L) (hgap : 0 < A₀-2*L)
    (hA : A₀*s ≤ A) (hell : ell ≤ L*s) :
    0 < A-2*ell ∧
      A/(A-2*ell)*exp (-(A-2*ell)) ≤ A₀/(A₀-2*L)*exp (-(A₀-2*L)) := by
  have hA₀ : 0 < A₀ := by linarith
  have hgrowth : A₀-2*L ≤ A-2*ell := by nlinarith
  have hg : 0 < A-2*ell := hgap.trans_le hgrowth
  have hAA : 0 < A := by nlinarith
  have hratio : A/(A-2*ell) ≤ A₀/(A₀-2*L) := by
    apply (div_le_div_iff₀ hg hgap).mpr
    nlinarith [mul_le_mul_of_nonneg_left hA hL,mul_le_mul_of_nonneg_left hell hA₀.le]
  refine ⟨hg,?_⟩
  exact mul_le_mul hratio (exp_le_exp.mpr (by linarith)) (exp_nonneg _) (div_nonneg hA₀.le hgap.le)

theorem sharp_cut_failure_two_scale {n : ℕ} {N u t ε lam A₀ L : ℝ} {k j : ℕ}
    (hn : 0 < n) (hN : 0 < N) (hu : 1 ≤ u) (ht : 1 ≤ t)
    (horder : (n:ℝ) ≤ N*u^k*t^j) (hlog : log N ≤ L)
    (hk : (k:ℝ) ≤ L) (hj : (j:ℝ) ≤ L)
    (hgap : 0 < A₀-2*L) (hA : A₀*(u*t) ≤ 2*ε^2*lam) :
    0 < 2*ε^2*lam-2*log (n:ℝ) ∧
      sharpCutFailure n ε lam ≤ A₀/(A₀-2*L)*exp (-(A₀-2*L)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hell := (log_le_log hnR horder).trans (log_two_scale_bound hN hu ht hlog hk hj)
  exact sharp_failure_scale_bound (by nlinarith) ((Nat.cast_nonneg k).trans hk) hgap hA hell

end
end Cycle13
