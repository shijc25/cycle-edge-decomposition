import Mathlib

/-! Finite probability laws with real weights. Explicit kernels will let
the sampling witness be exposed in either order without claiming
independence after conditioning on a successful event. -/
namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω=1

namespace FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def expect (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.mass ω*X ω
def prob (μ : FiniteLaw Ω) (E : Ω → Prop) : ℝ := μ.expect (fun ω => if E ω then 1 else 0)

theorem expect_mono (μ : FiniteLaw Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    μ.expect X ≤ μ.expect Y := sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem expect_nonneg (μ : FiniteLaw Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X :=
  sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (h ω))

@[simp] theorem expect_const (μ : FiniteLaw Ω) (c : ℝ) : μ.expect (fun _ => c)=c := by
  rw [expect,← sum_mul,μ.total,one_mul]

theorem expect_add (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω+Y ω)=μ.expect X+μ.expect Y := by
  simp only [expect,mul_add,sum_add_distrib]

theorem expect_mul_const (μ : FiniteLaw Ω) (X : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => X ω*c)=μ.expect X*c := by simp only [expect,mul_assoc,sum_mul]

theorem expect_const_mul (μ : FiniteLaw Ω) (X : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => c*X ω)=c*μ.expect X := by
  simp only [expect,mul_sum]; apply sum_congr rfl; intro ω _; ring

theorem expect_comm (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) (f : Ω → Ξ → ℝ) :
    μ.expect (fun ω => ν.expect (f ω))=ν.expect (fun ξ => μ.expect (fun ω => f ω ξ)) := by
  simp only [expect,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ξ _
  apply sum_congr rfl
  intro ω _
  ring

theorem expect_sum (μ : FiniteLaw Ω) {I : Type*} [Fintype I] (X : I → Ω → ℝ) :
    μ.expect (fun ω => ∑ i, X i ω)=∑ i, μ.expect (X i) := by
  simp only [expect,mul_sum]
  rw [sum_comm]

theorem prob_nonneg (μ : FiniteLaw Ω) (E : Ω → Prop) : 0 ≤ μ.prob E :=
  μ.expect_nonneg (fun ω => by split_ifs <;> norm_num)

theorem prob_le_one (μ : FiniteLaw Ω) (E : Ω → Prop) : μ.prob E ≤ 1 := by
  have hh := μ.expect_mono (X:=fun ω => if E ω then 1 else 0) (Y:=fun _ => 1)
    (fun ω => by split_ifs <;> norm_num)
  simpa only [prob,expect_const] using hh

theorem prob_mono (μ : FiniteLaw Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    μ.prob E ≤ μ.prob F := by
  apply μ.expect_mono
  intro ω; by_cases he : E ω
  · simp only [if_pos he,if_pos (h ω he),le_refl]
  · simp only [if_neg he]; split_ifs <;> norm_num

theorem prob_union_le (μ : FiniteLaw Ω) (E F : Ω → Prop) :
    μ.prob (fun ω => E ω ∨ F ω) ≤ μ.prob E+μ.prob F := by
  rw [prob,prob,prob,← expect_add]
  apply μ.expect_mono
  intro ω; by_cases he : E ω <;> by_cases hf : F ω <;> simp [he,hf]

theorem prob_exists_le_sum (μ : FiniteLaw Ω) {I : Type*} [Fintype I] (E : I → Ω → Prop) :
    μ.prob (fun ω => ∃ i, E i ω) ≤ ∑ i, μ.prob (E i) := by
  unfold prob expect
  rw [sum_comm]
  apply sum_le_sum
  intro ω _
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg ω)
  dsimp only
  split_ifs with h
  · obtain ⟨i,hi⟩ := h
    have hh := single_le_sum (s:=univ) (f:=fun i => if E i ω then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa only [if_pos hi] using hh
  · exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem exp_markov (μ : FiniteLaw Ω) (X : Ω → ℝ) (θ B : ℝ) (hθ : 0 < θ) :
    μ.prob (fun ω => B < X ω) ≤ exp (-θ*B)*μ.expect (fun ω => exp (θ*X ω)) := by
  rw [← expect_const_mul]
  apply μ.expect_mono
  intro ω
  by_cases h : B < X ω
  · simp only [if_pos h,← exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith
  · simp only [if_neg h]; positivity

theorem exp_markov_le (μ : FiniteLaw Ω) (X : Ω → ℝ) (θ B : ℝ) (hθ : 0 ≤ θ) :
    μ.prob (fun ω => B ≤ X ω) ≤ exp (-θ*B)*μ.expect (fun ω => exp (θ*X ω)) := by
  rw [← expect_const_mul]
  apply μ.expect_mono
  intro ω
  by_cases h : B ≤ X ω
  · simp only [if_pos h,← exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith
  · simp only [if_neg h]; positivity

def bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) : FiniteLaw Ξ where
  mass ξ := ∑ ω, μ.mass ω*(κ ω).mass ξ
  nonneg ξ := sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) ((κ ω).nonneg ξ))
  total := by
    rw [sum_comm]
    simp only [← mul_sum,FiniteLaw.total,mul_one,μ.total]

theorem expect_bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (X : Ξ → ℝ) :
    (μ.bind κ).expect X=μ.expect (fun ω => (κ ω).expect X) := by
  simp only [expect,bind,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp only [mul_sum,mul_assoc]

theorem witness_transfer (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (bad : Ω → Prop)
    (witness : Ω → Ξ → Prop) {p : ℝ} (hp : 0 ≤ p)
    (hgood : ∀ ω, bad ω → p ≤ (κ ω).prob (witness ω)) :
    p*μ.prob bad ≤ μ.expect (fun ω => (κ ω).prob (witness ω)) := by
  rw [prob,← expect_const_mul]
  apply μ.expect_mono
  intro ω
  by_cases h : bad ω
  · simpa only [if_pos h,mul_one] using hgood ω h
  · simpa only [if_neg h,mul_zero] using (κ ω).prob_nonneg (witness ω)

end FiniteLaw
end
end Cycle13
