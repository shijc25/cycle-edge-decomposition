import Cycle12.Foundations.WeakBranchBudget

/-! The infinite-range and small-order arithmetic of the 11t/10 branch
budget, including the integer ceiling. Existence of the carrier and its
balanced edge coloring is not assumed by this arithmetic theorem. -/
namespace Cycle13
open SimpleGraph

private theorem large_branch_polynomial {t p q : ℝ} (ht : 22 ≤ t)
    (hpq : p+q=t) (hq : 1 ≤ q) (hquarter : 4*q ≤ t-2) :
    10*q*(q-1) ≤ p*(t-10) := by
  have ha : 0 ≤ (t-2-4*q)*(t-6) := mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ (4*q)*(t-6-4*(q-1)) := mul_nonneg (by linarith) (by linarith)
  have hqprod : 16*q*(q-1) ≤ (t-2)*(t-6) := by nlinarith
  have hpbound : 3*t+2 ≤ 4*p := by linarith
  have hc := mul_le_mul_of_nonneg_right hpbound (by linarith : 0 ≤ t-10)
  have hquad : 0 ≤ t^2-16*t-100 := by nlinarith [sq_nonneg (t-22)]
  nlinarith

/-- This bound covers every even order, not just the finite experimental
range in the original Python audit. -/
theorem balanced_class_branch_budget {t p e : ℕ} (ht : 4 ≤ t) (heven : Even t)
    (hp : p < t) (hthree : 3*t < 4*p) (he : 2*e ≤ (t-p)*(t-p-1)) :
    10*(t-1+2*((e+p-1)/p)) ≤ 11*t := by
  have hp₀ : 0 < p := by omega
  have hq₁ : 1 ≤ t-p := by omega
  have hpq : p+(t-p)=t := Nat.add_sub_of_le hp.le
  obtain ⟨k, hk⟩ := heven
  have hquarter : 4*(t-p) ≤ t-2 := by omega
  let r := (e+p-1)/p
  have hceil : p*r ≤ e+p-1 := Nat.mul_div_le _ _
  have hp₁ : 1 ≤ e+p := by omega
  by_cases hlarge : 22 ≤ t
  · have hq₀ : (0:ℝ) ≤ (t-p:ℕ) := Nat.cast_nonneg _
    have hpoly := large_branch_polynomial
      (t := (t:ℝ)) (p := (p:ℝ)) (q := ((t-p:ℕ):ℝ))
      (by exact_mod_cast hlarge) (by exact_mod_cast hpq)
      (by exact_mod_cast hq₁) (by
        have h : 4*((t-p:ℕ):ℝ)+2 ≤ (t:ℝ) := by
          exact_mod_cast (show 4*(t-p)+2 ≤ t by omega)
        linarith)
    have heR : 2*(e:ℝ) ≤ ((t-p:ℕ):ℝ)*(((t-p:ℕ):ℝ)-1) := by
      exact_mod_cast he
    have hrR : (p:ℝ)*(r:ℝ) ≤ (e:ℝ)+(p:ℝ)-1 := by exact_mod_cast hceil
    have hpR : (0:ℝ) < p := by exact_mod_cast hp₀
    have hrbound : 20*(r:ℝ) ≤ (t:ℝ)+10 := by nlinarith
    have hrN : 20*r ≤ t+10 := by exact_mod_cast hrbound
    change 10*(t-1+2*r) ≤ 11*t
    omega
  · by_cases hsmall : t ≤ 8
    · have hq : t-p ≤ 1 := by omega
      have he₀ : e=0 := by
        have hzero : t-p-1=0 := by omega
        rw [hzero] at he
        omega
      have hr₀ : r=0 := by
        dsimp [r]
        rw [he₀, Nat.zero_add]
        exact Nat.div_eq_of_lt (by omega)
      change 10*(t-1+2*r) ≤ 11*t
      omega
    · have ht₁₀ : 10 ≤ t := by omega
      have hq₄ : t-p ≤ 4 := by omega
      have hprod : (t-p)*(t-p-1) ≤ 12 := by
        interval_cases hq : t-p <;> simp_all
      have hep : e ≤ p := by omega
      have hr₁ : r ≤ 1 := by
        have h : e+p-1 < 2*p := by omega
        have hdiv : (e+p-1)/p < 2 := (Nat.div_lt_iff_lt_mul hp₀).mpr h
        exact Nat.le_of_lt_succ hdiv
      change 10*(t-1+2*r) ≤ 11*t
      omega

/-- Interface from a balanced coloring's class size to actual weak-model
branch-edge usage. It does not assert the coloring or carrier exists. -/
theorem WeakCliqueImmersion.branch_budget_of_balanced_classes
    {V : Type} [Fintype V] {G : SimpleGraph V} {t p e : ℕ}
    (M : WeakCliqueImmersion t G) (ht : 4 ≤ t) (heven : Even t)
    (hp : p < t) (hthree : 3*t < 4*p) (he : 2*e ≤ (t-p)*(t-p-1))
    (hvisits : ∀ i, (M.internalVisits i).card ≤ (e+p-1)/p) (i : Fin t) :
    10*{f ∈ M.used | M.branch i ∈ f}.ncard ≤ 11*t := by
  classical
  rw [M.branch_used_edges]
  have h := balanced_class_branch_budget ht heven hp hthree he
  have hv := hvisits i
  omega

end Cycle13
