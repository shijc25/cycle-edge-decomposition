import Mathlib

namespace Cycle12
open Finset

theorem overlap_product_payment {I : Type*} (S : Finset I) (a : I → ℝ)
    (ha : ∀ i∈S, 0≤a i) (hS : ∑ i∈S, a i≤1) :
    (∏ i∈S, (1+a i))*(1-∑ i∈S, a i)≤1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hai := ha i (by simp)
    have haS : ∀ j∈S, 0≤a j := fun j hj => ha j (by simp [hj])
    have hs0 : 0≤∑ j∈S, a j := Finset.sum_nonneg haS
    have hp0 : 0≤∏ j∈S, (1+a j) := Finset.prod_nonneg (fun j hj => by linarith [haS j hj])
    rw [Finset.sum_insert hi] at hS
    have hS1 : ∑ j∈S, a j≤1 := by linarith only [hai,hS]
    have hh := ih haS hS1
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    have herr := mul_nonneg hp0 (mul_nonneg hai (add_nonneg hai hs0))
    nlinarith only [hh,herr]

theorem overlap_product_bound {I : Type*} (S : Finset I) (a : I → ℝ)
    (ha : ∀ i∈S, 0≤a i) {Z : ℝ} (hZ : ∑ i∈S, a i≤Z) (hZ1 : Z<1) :
    (∏ i∈S, (1+a i))≤1/(1-Z) := by
  have hcost := overlap_product_payment S a ha (hZ.trans hZ1.le)
  have hp0 : 0≤∏ i∈S, (1+a i) := Finset.prod_nonneg (fun i hi => by linarith [ha i hi])
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_left hZ 1) hp0
  apply (le_div_iff₀ (by linarith : 0<1-Z)).mpr
  exact hh.trans hcost

end Cycle12
