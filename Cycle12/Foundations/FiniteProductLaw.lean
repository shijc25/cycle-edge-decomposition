import Cycle12.Foundations.FiniteLaw

namespace Cycle13.FiniteLaw
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

def independent (κ : I → FiniteLaw Ω) : FiniteLaw (I → Ω) where
  mass x := ∏ i, (κ i).mass (x i)
  nonneg x := prod_nonneg (fun i _ => (κ i).nonneg _)
  total := by
    rw [← Fintype.prod_sum]
    simp only [FiniteLaw.total,prod_const_one]

theorem independent_expect_product (κ : I → FiniteLaw Ω) (f : I → Ω → ℝ) :
    (independent κ).expect (fun x => ∏ i, f i (x i))=∏ i, (κ i).expect (f i) := by
  simp only [expect,independent,← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => (κ i).mass ω*f i ω)).symm

theorem independent_expect_eval (κ : I → FiniteLaw Ω) (i : I) (f : Ω → ℝ) :
    (independent κ).expect (fun x => f (x i))=(κ i).expect f := by
  classical
  have hp : ∀ x : I→Ω, (∏ j, if j=i then f (x j) else 1)=f (x i) := by
    intro x; simp
  have hh := independent_expect_product κ (fun j ω => if j=i then f ω else 1)
  simp_rw [hp] at hh
  rw [hh]
  have he : ∀ j, (κ j).expect (fun ω => if j=i then f ω else 1)=
      if j=i then (κ i).expect f else 1 := by
    intro j; by_cases h : j=i
    · subst j; simp
    · simp only [h,ite_false,expect_const]
  simp_rw [he]
  simp

def uniformOn [DecidableEq Ω] (S : Finset Ω) (hS : S.Nonempty) : FiniteLaw Ω where
  mass ω := if ω∈S then 1/(S.card:ℝ) else 0
  nonneg ω := by split_ifs <;> positivity
  total := by
    rw [← sum_filter]
    have he : univ.filter (fun ω => ω∈S)=S := by ext ω; simp
    rw [he,sum_const,nsmul_eq_mul]
    have hc : (S.card:ℝ)≠0 := ne_of_gt (by exact_mod_cast hS.card_pos)
    field_simp

theorem uniformOn_expect [DecidableEq Ω] (S : Finset Ω) (hS : S.Nonempty) (f : Ω → ℝ) :
    (uniformOn S hS).expect f=(∑ ω∈S, f ω)/(S.card:ℝ) := by
  unfold expect uniformOn
  simp_rw [ite_mul,zero_mul]
  rw [← sum_filter]
  have he : univ.filter (fun ω => ω∈S)=S := by ext ω; simp
  rw [he,← mul_sum]
  ring

end
end Cycle13.FiniteLaw
