import Cycle12.Foundations.MarkedSamplingAtoms

/-! Reversing the sampling/marking order for every statistic of the
actual pair (sample, marked subset), by exact finite summation. -/
namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_expect (A : Finset V) (p : unitInterval) (f : Finset V → ℝ) :
    (subsetBernoulli A p).expect f=
      ∑ S∈A.powerset, (subsetBernoulli A p).mass S*f S := by
  apply (sum_subset (subset_univ _) ?_).symm
  intro S hS hno
  have hn : ¬S⊆A := fun h => hno (mem_powerset.mpr h)
  rw [subsetBernoulli_mass_not_subset _ _ _ hn,zero_mul]

theorem sum_supersets_sdiff (T : Finset V) (f : Finset V → ℝ) :
    (∑ U∈univ.filter (fun U : Finset V => T⊆U), f (U\T))=
      ∑ R∈(univ\T).powerset, f R := by
  apply sum_bij (fun U _ => U\T)
  · intro U hU
    exact mem_powerset.mpr (sdiff_subset_sdiff_left T (subset_univ U))
  · intro U hU W hW he
    have hu := (mem_filter.mp hU).2
    have hw := (mem_filter.mp hW).2
    calc
      U = T∪(U\T) := (union_sdiff_of_subset hu).symm
      _ = T∪(W\T) := congrArg (fun S => T∪S) he
      _ = W := union_sdiff_of_subset hw
  · intro R hR
    have hR := mem_powerset.mp hR
    refine ⟨T∪R,mem_filter.mpr ⟨mem_univ _,subset_union_left⟩,?_⟩
    ext v
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hv,hvT⟩; exact hv.resolve_left hvT
    · intro hv; exact ⟨Or.inr hv,(mem_sdiff.mp (hR hv)).2⟩
  · intro U hU; rfl

theorem remaining_union_expect (ρ : unitInterval) (T : Finset V) (f : Finset V → ℝ) :
    (∑ U : Finset V, (if T⊆U then (subsetBernoulli (univ\T) ρ).mass (U\T) else 0)*f U)=
      (subsetBernoulli (univ\T) ρ).expect (fun R => f (T∪R)) := by
  rw [subsetBernoulli_expect]
  have hp : ∀ U : Finset V,
      (if T⊆U then (subsetBernoulli (univ\T) ρ).mass (U\T) else 0)*f U=
      if T⊆U then (subsetBernoulli (univ\T) ρ).mass (U\T)*f (T∪(U\T)) else 0 := by
    intro U
    by_cases h : T⊆U
    · simp only [if_pos h,union_sdiff_of_subset h]
    · simp only [if_neg h,zero_mul]
  simp_rw [hp]
  rw [← sum_filter]
  exact sum_supersets_sdiff T (fun R => (subsetBernoulli (univ\T) ρ).mass R*f (T∪R))

theorem marked_sampling_order_reversal (p q markP ρ : unitInterval)
    (hmarkP : (markP:ℝ)=(p:ℝ)*(q:ℝ))
    (hρ : (1-(markP:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ))) (f : Finset V → Finset V → ℝ) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (f U))=
      (bernoulliSubset markP).expect (fun T => (subsetBernoulli (univ\T) ρ).expect
        (fun R => f (T∪R) T)) := by
  unfold FiniteLaw.expect
  simp_rw [mul_sum,← mul_assoc,marked_sampling_atom_identity p q markP ρ hmarkP hρ,mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  rw [← mul_sum,← mul_sum]
  congr 1
  exact remaining_union_expect ρ T (fun U => f U T)

end
end Cycle13
