import Cycle12.Foundations.FiniteSupport
import Cycle12.Foundations.FiniteCantelli

namespace Cycle13.FiniteLaw
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def joint (μ : FiniteLaw Ω) (κ : Ω→FiniteLaw Ξ) : FiniteLaw (Ω×Ξ) where
  mass x := μ.mass x.1*(κ x.1).mass x.2
  nonneg x := mul_nonneg (μ.nonneg _) ((κ _).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum,FiniteLaw.total,mul_one]

theorem expect_joint (μ : FiniteLaw Ω) (κ : Ω→FiniteLaw Ξ) (X : Ω×Ξ→ℝ) :
    (μ.joint κ).expect X=μ.expect (fun ω => (κ ω).expect (fun ξ => X (ω,ξ))) := by
  simp only [expect,joint,Fintype.sum_prod_type,mul_sum,mul_assoc]

theorem prob_joint (μ : FiniteLaw Ω) (κ : Ω→FiniteLaw Ξ) (E : Ω×Ξ→Prop) :
    (μ.joint κ).prob E=μ.expect (fun ω => (κ ω).prob (fun ξ => E (ω,ξ))) :=
  expect_joint _ _ _

theorem prob_joint_fst (μ : FiniteLaw Ω) (κ : Ω→FiniteLaw Ξ) (E : Ω→Prop) :
    (μ.joint κ).prob (fun x => E x.1)=μ.prob E := by
  rw [prob_joint]
  unfold prob
  congr 1
  funext ω
  by_cases h : E ω <;> simp [h]

theorem prob_gt_le_expect_div (μ : FiniteLaw Ω) (X : Ω→ℝ)
    (hX : ∀ ω, 0≤X ω) {t : ℝ} (ht : 0<t) :
    μ.prob (fun ω => t<X ω) ≤ μ.expect X/t := by
  apply (μ.prob_mono (fun ω h => h.le)).trans
  apply (le_div_iff₀ ht).mpr
  have hh := μ.markov_mul X hX t
  linarith

theorem prob_good_weight (μ : FiniteLaw Ω) (X : Ω→ℝ) (bad : Ω→Prop)
    (hX : ∀ ω, 0≤X ω) {t : ℝ} (ht : 0<t) :
    1-μ.expect X/t-μ.prob bad ≤ μ.prob (fun ω => X ω≤t ∧ ¬bad ω) := by
  have he : (fun ω => X ω≤t ∧ ¬bad ω)=(fun ω => ¬(t<X ω ∨ bad ω)) := by
    funext ω; apply propext; simp only [not_or,not_lt]
  rw [he,prob_compl]
  have hu := μ.prob_union_le (fun ω => t<X ω) bad
  have hm := μ.prob_gt_le_expect_div X hX ht
  linarith

end
end Cycle13.FiniteLaw
