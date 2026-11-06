import Cycle12.BernoulliLaplaceCorrelation

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def occurrenceCount (E : I → Finset V) (S : Finset V) : ℝ :=
  ∑ i, containsIndicator (E i) S

def occurrencePart (E : I → Finset V) (K : Finset I) (S : Finset V) : ℝ :=
  ∑ i ∈ K, containsIndicator (E i) S

theorem contains_indicator_nonneg (A S : Finset V) : 0 ≤ containsIndicator A S := by
  unfold containsIndicator
  split_ifs <;> norm_num

theorem contains_indicator_monotone (A : Finset V) : Monotone (containsIndicator A) := by
  intro S T hST
  unfold containsIndicator
  by_cases hAS : A⊆S
  · rw [if_pos hAS,if_pos (hAS.trans hST)]
  · rw [if_neg hAS]
    split_ifs <;> norm_num

theorem occurrence_part_nonneg (E : I → Finset V) (K : Finset I) (S : Finset V) :
    0 ≤ occurrencePart E K S := sum_nonneg (fun i _ => contains_indicator_nonneg _ _)

theorem occurrence_part_monotone (E : I → Finset V) (K : Finset I) :
    Monotone (occurrencePart E K) := by
  intro S T hST
  exact sum_le_sum (fun i _ => contains_indicator_monotone (E i) hST)

theorem occurrence_part_partition (E : I → Finset V) (K : Finset I) (S : Finset V) :
    occurrenceCount E S=occurrencePart E K S+occurrencePart E Kᶜ S := by
  exact (sum_add_sum_compl K (fun i => containsIndicator (E i) S)).symm

theorem contains_indicator_ignore (A B S : Finset V) (hAB : Disjoint A B) :
    containsIndicator B S=containsIndicator B (S\A) := by
  have he : B⊆S ↔ B⊆S\A := by
    refine ⟨?_,fun h => h.trans sdiff_subset⟩
    intro h v hv
    exact mem_sdiff.mpr ⟨h hv,fun hvA => disjoint_left.mp hAB hvA hv⟩
  simp only [containsIndicator,he]

theorem occurrence_part_ignore (E : I → Finset V) (K : Finset I) (A : Finset V)
    (hd : ∀ i ∈ K, Disjoint A (E i)) (S : Finset V) :
    occurrencePart E K S=occurrencePart E K (S\A) := by
  exact sum_congr rfl (fun i hi => contains_indicator_ignore A (E i) S (hd i hi))

theorem subset_bernoulli_contains_expect (D A : Finset V) (hA : A⊆D) (p : unitInterval) :
    (subsetBernoulli D p).expect (containsIndicator A)=(p:ℝ)^A.card := by
  have hh := bernoulli_condition_expect D A hA p (fun _ => (1:ℝ))
  have he : containsIndicator A=(fun S : Finset V => if A⊆S then (1:ℝ) else 0) := by
    funext S
    unfold containsIndicator
    split_ifs <;> rfl
  rw [he]
  simpa only [mul_one,FiniteLaw.expect_const] using hh

theorem subset_bernoulli_contains_product (D A B : Finset V) (hA : A⊆D) (hB : B⊆D)
    (p : unitInterval) :
    (subsetBernoulli D p).expect (fun S => containsIndicator A S*containsIndicator B S)=
      (p:ℝ)^(A∪B).card := by
  simp_rw [containsIndicator_mul]
  exact subset_bernoulli_contains_expect D (A∪B) (union_subset hA hB) p

/-- The weighted conditional dependent count is an exact ordered-pair sum. -/
theorem occurrence_conditional_mean (D : Finset V) (E : I → Finset V)
    (hE : ∀ i, E i⊆D) (K : Finset I) (i : I) (p : unitInterval) :
    (p:ℝ)^(E i).card*(subsetBernoulli (D\E i) p).expect
        (fun R => occurrencePart E K (E i∪R)) =
      ∑ j ∈ K, (p:ℝ)^(E i∪E j).card := by
  rw [← bernoulli_condition_expect D (E i) (hE i) p (occurrencePart E K)]
  unfold occurrencePart FiniteLaw.expect
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hh := subset_bernoulli_contains_product D (E i) (E j) (hE i) (hE j) p
  simpa only [FiniteLaw.expect,containsIndicator,mul_assoc] using hh

end
end Cycle12
