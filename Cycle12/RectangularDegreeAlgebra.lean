import Cycle12.FiniteLaplace

namespace Cycle12
open Finset
noncomputable section
variable {I : Type} [Fintype I]

theorem rectangular_min_pair_bound (C a b : ℝ) (ha0 : 0≤a) (hb0 : 0≤b)
    (ha : a≤C) (hb : b≤C) :
    2*C*min a b+(a-b)^2 ≤ C*(a+b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0≤C-b+a by linarith)]
  · rw [min_eq_right hba]
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (show 0≤C-a+b by linarith)]

theorem sum_pair_squared_differences (d : I → ℝ) :
    (∑ i, ∑ j, (d i-d j)^2)=
      2*(Fintype.card I:ℝ)*(∑ i, (d i)^2)-2*(∑ i, d i)^2 := by
  simp_rw [sub_sq,sum_add_distrib,sum_sub_distrib]
  simp only [sum_const,card_univ,nsmul_eq_mul,← mul_sum,← sum_mul]
  ring

/-- Purely scalar form of the rectangular degree-square inequality.
Only the number and maximum size of the rows are constrained. -/
theorem rectangular_degree_square_algebra (d : I → ℝ) (C : ℝ)
    (hC : 0<C) (hu : (Fintype.card I:ℝ)≤C)
    (hd0 : ∀ i, 0≤d i) (hdC : ∀ i, d i≤C) :
    (∑ i, (d i)^2)+(∑ i, ∑ j, min (d i) (d j)) ≤
      C*(∑ i, d i)+(∑ i, d i)^2/C := by
  have hp := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ)
    (fun j _ => rectangular_min_pair_bound C (d i) (d j) (hd0 i) (hd0 j) (hdC i) (hdC j)))
  have he : (∑ i, ∑ j, (2*C*min (d i) (d j)+(d i-d j)^2))=
      2*C*(∑ i, ∑ j, min (d i) (d j))+
        2*(Fintype.card I:ℝ)*(∑ i, (d i)^2)-2*(∑ i, d i)^2 := by
    simp only [sum_add_distrib,← mul_sum,sum_pair_squared_differences]
    ring
  have hr : (∑ i, ∑ j, C*(d i+d j))=2*C*(Fintype.card I:ℝ)*(∑ i, d i) := by
    simp only [mul_add,sum_add_distrib,← mul_sum,sum_const,card_univ,nsmul_eq_mul,← sum_mul]
    ring
  rw [he,hr] at hp
  have hsq : (∑ i, (d i)^2) ≤ C*(∑ i, d i) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    nlinarith [mul_nonneg (hd0 i) (sub_nonneg.mpr (hdC i))]
  have hx := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hu)
  have hc : C*((∑ i, d i)^2/C)=(∑ i, d i)^2 := by field_simp
  nlinarith

end
end Cycle12
