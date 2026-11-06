import Mathlib

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

theorem capped_degree_sum_lower_bound (S : Finset V) (d : V→ℕ) (k : ℕ) (a : ℝ)
    (hcut : ∀ X⊆S, a*X.card ≤ (∑ v∈X, (d v:ℝ))+(X.card:ℝ)*(S.card-X.card)) :
    a*S.card-(max (a+(S.card:ℝ)-k) 0)^2/4 ≤ ∑ v∈S, ((min k (d v):ℕ):ℝ) := by
  let X := S.filter (fun v => d v≤k)
  let C := S\X
  have hXS : X⊆S := filter_subset _ _
  have hcard : (X.card:ℝ)+(C.card:ℝ)=S.card := by
    have hh := card_sdiff_add_card_eq_card hXS
    change C.card+X.card=S.card at hh
    exact_mod_cast (by omega : X.card+C.card=S.card)
  have he : (∑ v∈S, ((min k (d v):ℕ):ℝ))=(∑ v∈X, (d v:ℝ))+(k:ℝ)*C.card := by
    have hh := sum_union (f:=fun v => ((min k (d v):ℕ):ℝ))
      (show Disjoint X (S\X) from disjoint_sdiff_self_right)
    rw [union_sdiff_of_subset hXS] at hh
    rw [hh]
    have hx : (∑ v∈X, ((min k (d v):ℕ):ℝ))=∑ v∈X, (d v:ℝ) := by
      exact sum_congr rfl (fun v hv => by rw [min_eq_right (mem_filter.mp hv).2])
    have hc : (∑ v∈S\X, ((min k (d v):ℕ):ℝ))=(k:ℝ)*C.card := by
      have hp : ∀ v∈S\X, min k (d v)=k := by
        intro v hv
        have hh := mem_sdiff.mp hv
        have hn : ¬d v≤k := fun h => hh.2 (mem_filter.mpr ⟨hh.1,h⟩)
        exact min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      rw [sum_congr rfl (fun v hv => congrArg (fun n : ℕ => (n:ℝ)) (hp v hv))]
      simp only [sum_const,nsmul_eq_mul]
      change (C.card:ℝ)*k=(k:ℝ)*C.card
      ring
    rw [hx,hc]
  have hc := hcut X hXS
  have hC : 0≤(C.card:ℝ) := Nat.cast_nonneg _
  rw [he]
  by_cases hb : 0≤a+(S.card:ℝ)-k
  · rw [max_eq_left hb]
    nlinarith [sq_nonneg (2*(C.card:ℝ)-(a+(S.card:ℝ)-k))]
  · rw [max_eq_right (le_of_not_ge hb)]
    have hp : 0≤(C.card:ℝ)*((k:ℝ)-a-S.card) := mul_nonneg hC (by linarith)
    nlinarith [sq_nonneg (C.card:ℝ)]

end
end Cycle13
