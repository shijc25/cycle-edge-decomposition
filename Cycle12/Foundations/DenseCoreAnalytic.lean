import Mathlib

/-! Analytic heart of the dense strong-immersion peeling argument.
The extraction of a graph core and the immersion theorem are separate obligations.
We multiply the potential by `x` and use concavity of `-x log x`.
-/
namespace Cycle13
open Set Real

noncomputable def denseCorePotential (E N D T x : ℝ) : ℝ :=
  2 * D * x - 2 * (D * N - E) - T * x * (1 + log (x / T))

theorem denseCorePotential_concave (E N D T : ℝ) (hT : 0 < T) :
    ConcaveOn ℝ (Ici (0 : ℝ)) (denseCorePotential E N D T) := by
  have ha : ConcaveOn ℝ (Ici (0 : ℝ))
      (fun x => (2 * D - T + T * log T) * x - 2 * (D * N - E)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    apply le_of_eq
    calc
      _ = (2 * D - T + T * log T) * (a * x + b * y) -
          (a + b) * (2 * (D * N - E)) := by ring
      _ = _ := by rw [hab, one_mul]
  have hc := ha.sub (ConvexOn.smul hT.le Real.convexOn_mul_log)
  apply hc.congr
  intro x hx
  simp only [Pi.sub_apply, smul_eq_mul, denseCorePotential]
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [Real.log_div hx0 hT.ne']
    ring

theorem dense_core_retained_average_bound {E N D T n : ℝ}
    (hT : 0 < T) (hTD : T ≤ D) (hDn : D ≤ n) (hnN : n ≤ N)
    (hE : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + log (N / T)) ≤ 2 * E / N) :
    T * (1 + log (n / T)) ≤ 2 * (E - D * (N - n)) / n := by
  have hD : 0 < D := hT.trans_le hTD
  have hn : 0 < n := hD.trans_le hDn
  have hN : 0 < N := hn.trans_le hnN
  have hlog := Real.log_le_sub_one_of_pos (div_pos hD hT)
  have hmul := mul_le_mul_of_nonneg_left hlog hT.le
  have hcancel : T * (D / T) = D := by field_simp
  have hlogD : T * (1 + log (D / T)) ≤ D := by nlinarith
  have hleft : 0 ≤ denseCorePotential E N D T D := by
    unfold denseCorePotential
    have hh := mul_le_mul_of_nonneg_right hlogD hD.le
    nlinarith
  have hright : 0 ≤ denseCorePotential E N D T N := by
    have hh := (le_div_iff₀ hN).mp hstop
    unfold denseCorePotential
    nlinarith
  have hmid := (denseCorePotential_concave E N D T hT).min_le_of_mem_Icc
    hD.le hN.le (show n ∈ Icc D N from ⟨hDn, hnN⟩)
  have hp : 0 ≤ denseCorePotential E N D T n :=
    (le_min hleft hright).trans hmid
  apply (le_div_iff₀ hn).mpr
  unfold denseCorePotential at hp
  nlinarith

theorem dense_core_average_bound {E N D T n m : ℝ}
    (hT : 0 < T) (hTD : T ≤ D) (hDn : D ≤ n) (hnN : n ≤ N)
    (hE : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + log (N / T)) ≤ 2 * E / N)
    (hretained : E - D * (N - n) ≤ m) :
    T * (1 + log (n / T)) ≤ 2 * m / n := by
  have hn : 0 < n := (hT.trans_le hTD).trans_le hDn
  apply (dense_core_retained_average_bound hT hTD hDn hnN hE hstop).trans
  exact div_le_div_of_nonneg_right (by linarith) hn.le

/-- The clique stopping expression is strictly increasing below the graph order. -/
theorem stopping_expression_strict_mono {a b n : ℝ}
    (ha : 0 < a) (hab : a < b) (hbn : b < n) :
    a * (1 + log (n / a)) < b * (1 + log (n / b)) := by
  have hb : 0 < b := ha.trans hab
  have hn : 0 < n := hb.trans hbn
  have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hm := mul_le_mul_of_nonneg_left hl ha.le
  have hcancel : a * (b / a) = b := by field_simp
  have hlog : log (n / a) = log (n / b) + log (b / a) := by
    rw [Real.log_div hn.ne' ha.ne', Real.log_div hn.ne' hb.ne',
      Real.log_div hb.ne' ha.ne']
    ring
  have hpos : 0 < (b - a) * log (n / b) := by
    apply mul_pos (sub_pos.mpr hab)
    exact Real.log_pos ((one_lt_div hb).mpr hbn)
  rw [hlog]
  nlinarith

/-- Strictness needed to use the inherited splitting stopping criterion. -/
theorem strict_stopping_threshold {a T n : ℝ}
    (ha : 0 < a) (haT : a < T) (hTn : T < n) (hn : 1 < n) :
    a * (1 + log ((n - 1) / a)) < T * (1 + log (n / T)) := by
  have hlog : log ((n - 1) / a) ≤ log (n / a) := by
    apply Real.log_le_log (div_pos (by linarith) ha)
    exact div_le_div_of_nonneg_right (by linarith) ha.le
  calc
    _ ≤ a * (1 + log (n / a)) := by gcongr
    _ < _ := stopping_expression_strict_mono ha haT hTn

end Cycle13
