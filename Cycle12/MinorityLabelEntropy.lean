import Cycle12.FixedMarkedUnion
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem minority_labels_exponential_bound (T : Finset V) {a theta : ℝ} (ht : theta ≤ 0) :
    (((T.powerset.filter (fun A => (A.card:ℝ) ≤ a)).card):ℝ) ≤
      exp (-theta*a)*(1+exp theta)^T.card := by
  let F := T.powerset.filter (fun A => (A.card:ℝ) ≤ a)
  have hpoint : (F.card:ℝ)*exp (theta*a) ≤ ∑ A∈F, exp (theta*A.card) := by
    calc
      _ = ∑ _A∈F, exp (theta*a) := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ _ := sum_le_sum (fun A hA => exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (mem_filter.mp hA).2 ht))
  have hsum : (∑ A∈F, exp (theta*A.card)) ≤ ∑ A∈T.powerset, exp (theta*A.card) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (exp_pos _).le)
  rw [label_exponential_sum] at hsum
  have hh := hpoint.trans hsum
  have he := mul_le_mul_of_nonneg_right hh (exp_pos (-theta*a)).le
  have hcancel : exp (theta*a)*exp (-theta*a)=1 := by rw [← exp_add]; simp
  calc
    (F.card:ℝ) = ((F.card:ℝ)*exp (theta*a))*exp (-theta*a) := by rw [mul_assoc,hcancel,mul_one]
    _ ≤ (1+exp theta)^T.card*exp (-theta*a) := he
    _ = _ := mul_comm _ _

theorem entropy_exponential_identity (rho : ℝ) (n : ℕ) (hr : 0 < rho) (hr1 : rho < 1) :
    exp (-log (rho/(1-rho))*(rho*n))*(1+exp (log (rho/(1-rho))))^n =
      exp ((n:ℝ)*binEntropy rho) := by
  have hcomp : 0 < 1-rho := sub_pos.mpr hr1
  rw [exp_log (div_pos hr hcomp)]
  have hbase : 1+rho/(1-rho)=(1-rho)⁻¹ := by field_simp; ring
  rw [hbase]
  have he : ((1-rho)⁻¹)^n=exp ((n:ℝ)*log ((1-rho)⁻¹)) := by
    rw [exp_nat_mul,exp_log (inv_pos.mpr hcomp)]
  rw [he,← exp_add,log_div hr.ne' hcomp.ne',log_inv,binEntropy,log_inv,log_inv]
  congr 1
  ring

/-- Entropy count for minority labels, including the empty mark set and
the endpoint rho=1/2. No independence of label-dependent graphs is used. -/
theorem minority_labels_entropy_bound (T : Finset V) {rho : ℝ}
    (hr : 0 < rho) (hrhalf : rho ≤ 1/2) :
    (((T.powerset.filter (fun A => (A.card:ℝ) ≤ rho*T.card)).card):ℝ) ≤
      exp ((T.card:ℝ)*binEntropy rho) := by
  have hr1 : rho < 1 := by linarith
  have hrcomp : 0 < 1-rho := by linarith
  have hratio : rho/(1-rho) ≤ 1 := (div_le_one hrcomp).mpr (by linarith)
  have ht : log (rho/(1-rho)) ≤ 0 := log_nonpos (div_nonneg hr.le hrcomp.le) hratio
  have hh := minority_labels_exponential_bound T (a:=rho*T.card) ht
  rwa [entropy_exponential_identity rho T.card hr hr1] at hh

end
end Cycle12
