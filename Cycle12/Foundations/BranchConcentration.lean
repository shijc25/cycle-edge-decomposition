import Mathlib

/-! Uniform degree control before the branch set is selected. -/
namespace Cycle13
open Finset Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section

theorem hoeffding_unit_lower_tail {Ω I : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : I → Ω → ℝ}
    (s : Finset I) (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hbound : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {q a : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = q) (ha : 0 ≤ a) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ q * s.card - a} ≤
      exp (-2 * a ^ 2 / s.card) := by
  let Y : I → Ω → ℝ := fun i ω => q - X i ω
  have hiY : iIndepFun Y μ := hi.comp (fun _ x => q - x) (fun _ => by fun_prop)
  have hY : ∀ i ∈ s, HasSubgaussianMGF (Y i) (1/4 : ℝ≥0) μ := by
    intro i _
    have hs := (hasSubgaussianMGF_of_mem_Icc (hm i).aemeasurable
      (ae_of_all μ (hbound i))).neg
    have hn : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1/4 := by norm_num
    rw [hn] at hs
    rw [hmean i] at hs
    convert hs using 1
    funext ω
    simp only [Y, Pi.neg_apply, neg_sub]
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hiY hY ha
  have he : {ω | (∑ i ∈ s, X i ω) ≤ q * s.card - a} =
      {ω | a ≤ ∑ i ∈ s, Y i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Y, sum_sub_distrib, sum_const, nsmul_eq_mul]
    constructor <;> intro h <;> nlinarith
  rw [he]
  convert h using 1
  simp only [sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  congr 1
  ring

theorem hoeffding_unit_relative_lower_tail {Ω I : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : I → Ω → ℝ}
    (s : Finset I) (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hbound : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {q ε : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = q) (hε : 0 ≤ ε) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ (q - ε) * s.card} ≤
      exp (-2 * ε ^ 2 * s.card) := by
  have h := hoeffding_unit_lower_tail s hm hi hbound hmean
    (mul_nonneg hε (Nat.cast_nonneg s.card))
  have he : q * (s.card : ℝ) - ε * s.card = (q - ε) * s.card := by ring
  rw [he] at h
  convert h using 1
  congr 1
  by_cases hs : s.card = 0
  · simp [hs]
  · have hsR : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    field_simp

/-- The worst threshold is at `d = D/(1-g)`. This algebraic proof
avoids differentiating a quotient separately on each side. -/
theorem branch_threshold_exponent {D d q g : ℝ}
    (hD : 0 < D) (hd : 0 < d) (hg₀ : 0 ≤ g) (hgq : g < q) (hq₁ : q ≤ 1)
    (hDd : D ≤ d) :
    2 * D * (q - g) ^ 2 / (1 - g) ≤
      2 * (q * d - min (g * d) (d - D)) ^ 2 / d := by
  have hg₁ : g < 1 := hgq.trans_le hq₁
  have hgp : 0 < 1 - g := by linarith
  by_cases hcase : D ≤ (1 - g) * d
  · have hmin : min (g * d) (d - D) = g * d := min_eq_left (by nlinarith)
    rw [hmin]
    have hc : D / (1 - g) ≤ d := (div_le_iff₀ hgp).mpr (by nlinarith)
    have hb := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2 * (q - g) ^ 2 by positivity)
    convert hb using 1 <;> field_simp <;> ring
  · have hmin : min (g * d) (d - D) = d - D := min_eq_right (by nlinarith)
    rw [hmin]
    have hr : 0 ≤ D - (1 - g) * d := by linarith
    have hqg : 0 < q - g := by linarith
    have hq0 : 0 ≤ 1 - q := by linarith
    have h1 := mul_nonneg hr (show 0 ≤ D * (1 - g) - d * (1 - q) ^ 2 by
      have hp := mul_nonneg (show 0 ≤ (1 - g) - (1 - q) by linarith)
        (show 0 ≤ (1 - g) + (1 - q) by linarith)
      nlinarith)
    apply (div_le_div_iff₀ hgp hd).mpr
    nlinarith

theorem conditional_degree_failure {Ω I : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : I → Ω → ℝ}
    (s : Finset I) (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hbound : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {D q g : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = q)
    (hD : 0 < D) (hg₀ : 0 ≤ g) (hgq : g < q) (hq₁ : q ≤ 1) :
    μ.real {ω | D ≤ (s.card : ℝ) - (∑ i ∈ s, X i ω) ∧
      (∑ i ∈ s, X i ω) < g * s.card} ≤
        exp (-2 * D * (q - g) ^ 2 / (1 - g)) := by
  by_cases hDd : D ≤ (s.card : ℝ)
  · have hd : (0 : ℝ) < s.card := hD.trans_le hDd
    let a : ℝ := q * s.card - min (g * s.card) (s.card - D)
    have ha : 0 ≤ a := by
      have hm := min_le_left (g * s.card) ((s.card : ℝ) - D)
      have hp := mul_pos (sub_pos.mpr hgq) hd
      dsimp only [a]
      nlinarith
    have hsub : {ω | D ≤ (s.card : ℝ) - (∑ i ∈ s, X i ω) ∧
        (∑ i ∈ s, X i ω) < g * s.card} ⊆
        {ω | (∑ i ∈ s, X i ω) ≤ q * s.card - a} := by
      intro ω hω
      change (∑ i ∈ s, X i ω) ≤ q * s.card - a
      dsimp only [a]
      have hm : (∑ i ∈ s, X i ω) ≤ min (g * s.card) ((s.card : ℝ) - D) :=
        le_min hω.2.le (by linarith [hω.1])
      linarith
    refine (measureReal_mono hsub).trans ((hoeffding_unit_lower_tail s hm hi hbound hmean ha).trans ?_)
    apply Real.exp_le_exp.mpr
    have h := branch_threshold_exponent hD hd hg₀ hgq hq₁ hDd
    change -2 * a ^ 2 / s.card ≤ -2 * D * (q - g) ^ 2 / (1 - g)
    dsimp only [a]
    convert neg_le_neg h using 1 <;> ring
  · have he : {ω | D ≤ (s.card : ℝ) - (∑ i ∈ s, X i ω) ∧
        (∑ i ∈ s, X i ω) < g * s.card} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hn : 0 ≤ ∑ i ∈ s, X i ω := sum_nonneg (fun i _ => (hbound i ω).1)
      exact hDd (by linarith [hω.1])
    rw [he, measureReal_empty]
    exact (exp_pos _).le

/-- This controls all potential branches in one experiment. No independence
between the vertex bad events is assumed or needed. -/
theorem uniform_conditional_degree_failure {Ω I V : Type} [MeasurableSpace Ω] [Fintype V]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : I → Ω → ℝ}
    (s : V → Finset I) (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hbound : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {D q g : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = q)
    (hD : 0 < D) (hg₀ : 0 ≤ g) (hgq : g < q) (hq₁ : q ≤ 1) :
    μ.real {ω | ∃ v : V, D ≤ ((s v).card : ℝ) - (∑ i ∈ s v, X i ω) ∧
      (∑ i ∈ s v, X i ω) < g * (s v).card} ≤
        Fintype.card V * exp (-2 * D * (q - g) ^ 2 / (1 - g)) := by
  have he : {ω | ∃ v : V, D ≤ ((s v).card : ℝ) - (∑ i ∈ s v, X i ω) ∧
      (∑ i ∈ s v, X i ω) < g * (s v).card} =
      ⋃ v : V, {ω | D ≤ ((s v).card : ℝ) - (∑ i ∈ s v, X i ω) ∧
        (∑ i ∈ s v, X i ω) < g * (s v).card} := by ext; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _v : V, exp (-2 * D * (q - g) ^ 2 / (1 - g)) :=
      sum_le_sum (fun v _ => conditional_degree_failure (s v) hm hi hbound hmean hD hg₀ hgq hq₁)
    _ = _ := by simp

end
end Cycle13
