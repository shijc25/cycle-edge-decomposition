import Cycle12.Foundations.MixedCoverBudget
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Cycle13.MixedSample
open Real Finset
noncomputable section

theorem rpow_three_halves {n : ℝ} (hn : 0 ≤ n) : n^(3/2:ℝ)=n*sqrt n := by
  rcases eq_or_lt_of_le hn with he | hp
  · rw [← he]
    norm_num
  · rw [show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hp,rpow_one,← sqrt_eq_rpow]

/-- The sharp two-piece Hölder estimate used when removing a sparse cut. -/
theorem split_cube_budget {n₁ n₂ m₁ m₂ : ℝ}
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂) :
    n₁*cubeScale m₁+n₂*cubeScale m₂ ≤
      (n₁*sqrt n₁+n₂*sqrt n₂)^(2/3:ℝ)*cubeScale (m₁+m₂) := by
  have hconj : Real.HolderConjugate (3/2:ℝ) 3 := by
    norm_num [Real.holderConjugate_iff]
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s:=(univ : Finset (Fin 2)))
    (f:=![n₁,n₂]) (g:=![cubeScale m₁,cubeScale m₂]) hconj
    (by intro i _; fin_cases i; exact hn₁; exact hn₂)
    (by intro i _; fin_cases i; exact rpow_nonneg hm₁ _; exact rpow_nonneg hm₂ _)
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    rpow_three_halves hn₁,rpow_three_halves hn₂] at hh
  have hc₁ : (cubeScale m₁)^(3:ℝ)=m₁ := by
    rw [show (3:ℝ)=((3:ℕ):ℝ) from rfl,Real.rpow_natCast,cubeScale_cube hm₁]
  have hc₂ : (cubeScale m₂)^(3:ℝ)=m₂ := by
    rw [show (3:ℝ)=((3:ℕ):ℝ) from rfl,Real.rpow_natCast,cubeScale_cube hm₂]
  rw [hc₁,hc₂] at hh
  norm_num only [one_div,inv_div,one_mul] at hh
  simpa only [cubeScale,one_div] using hh

theorem cube_deletion_tangent {e m : ℝ} (hm : 0 < m) (he : 0 ≤ e) (hem : e ≤ m) :
    cubeScale (1-e/m) ≤ 1-e/(3*m) := by
  have hr := (div_le_one hm).mpr hem
  have hh := rpow_one_add_le_one_add_mul_self (s:=-(e/m)) (by linarith)
    (by norm_num : (0:ℝ) ≤ (3:ℝ)⁻¹) (by norm_num : (3:ℝ)⁻¹ ≤ 1)
  unfold cubeScale
  convert hh using 1 <;> ring

/-- A sparse cut can be charged exactly to the lost mixed residual budget. -/
theorem sparse_cut_payment {FB FA U S e m : ℝ}
    (hFB : 0 ≤ FB) (hU : 0 ≤ U) (hm : 0 < m) (he : 0 ≤ e) (hem : e ≤ m)
    (hden : 0 < 1-FB*U/(3*m))
    (hcut : e ≤ (FB*(1-U)+FA*(1-S))/(1-FB*U/(3*m))) :
    e+FB*U*cubeScale (1-e/m)+FA*S ≤ FB+FA := by
  have hh := (le_div_iff₀ hden).mp hcut
  have hroot := mul_le_mul_of_nonneg_left (cube_deletion_tangent hm he hem) (mul_nonneg hFB hU)
  calc
    _ ≤ e+FB*U*(1-e/(3*m))+FA*S := by linarith
    _ = e*(1-FB*U/(3*m))+FB*U+FA*S := by ring
    _ ≤ _ := by linarith only [hh]

end
end Cycle13.MixedSample
