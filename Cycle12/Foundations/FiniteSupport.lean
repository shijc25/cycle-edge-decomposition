import Cycle12.Foundations.FiniteLaw

namespace Cycle13.FiniteLaw
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

theorem expect_mono_support (μ : FiniteLaw Ω) {X Y : Ω→ℝ}
    (h : ∀ ω, 0<μ.mass ω → X ω≤Y ω) : μ.expect X≤μ.expect Y := by
  apply sum_le_sum
  intro ω _
  by_cases hz : μ.mass ω=0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (h ω (lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hz))) (μ.nonneg ω)

theorem prob_mono_support (μ : FiniteLaw Ω) {E F : Ω→Prop}
    (h : ∀ ω, 0<μ.mass ω → E ω → F ω) : μ.prob E≤μ.prob F := by
  apply μ.expect_mono_support
  intro ω hω
  by_cases he : E ω
  · simp [he,h ω hω he]
  · simp only [he,ite_false]; split_ifs <;> norm_num

theorem expect_finset_sum (μ : FiniteLaw Ω) {I : Type*} (S : Finset I) (X : I→Ω→ℝ) :
    μ.expect (fun ω => ∑ i∈S, X i ω)=∑ i∈S, μ.expect (X i) := by
  simp only [expect,mul_sum]
  rw [sum_comm]

theorem prob_compl (μ : FiniteLaw Ω) (E : Ω→Prop) :
    μ.prob (fun ω => ¬E ω)=1-μ.prob E := by
  have hh : μ.prob E+μ.prob (fun ω => ¬E ω)=1 := by
    rw [prob,prob,← expect_add]
    calc
      _ = μ.expect (fun _ => 1) := by
        congr 1
        funext ω
        by_cases h : E ω <;> simp [h]
      _ = 1 := μ.expect_const _
  linarith

theorem exists_all_good (μ : FiniteLaw Ω) {I : Type*} [Fintype I]
    (bad : I→Ω→Prop) (bound : I→ℝ) (hbound : ∀ i, μ.prob (bad i)≤bound i)
    (hsum : ∑ i, bound i<1) : ∃ ω, ∀ i, ¬bad i ω := by
  by_contra! h
  have he : μ.prob (fun ω => ∃ i, bad i ω)=1 := by
    unfold prob
    simp only [h,ite_true,expect_const]
  have hh := μ.prob_exists_le_sum bad
  rw [he] at hh
  have hb := sum_le_sum (s:=univ) (fun i _ => hbound i)
  linarith

end
end Cycle13.FiniteLaw
