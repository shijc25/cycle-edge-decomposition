import Cycle12.FixedSampleMGF
import Cycle12.BernoulliOccurrence

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_size_contains_all (D S : Finset V) (hS : S⊆D) {k : ℕ} (hk : k≤D.card) :
    (fixedSizeLaw D k).prob (fun T => S⊆T)=(k.choose S.card:ℝ)/(D.card.choose S.card:ℝ) := by
  by_cases hSk : S.card≤k
  · exact fixed_size_contains_symmetric D S hS hk hSk
  · have hz : (fixedSizeLaw D k).prob (fun T => S⊆T)=0 := by
      apply le_antisymm _ (FiniteLaw.prob_nonneg _ _)
      calc
        _ ≤ (fixedSizeLaw D k).prob (fun _ => False) := by
          apply FiniteLaw.prob_mono_support
          intro T hT hST
          have ht := (fixed_size_support D T hk hT).2
          exact hSk (ht ▸ card_le_card hST)
        _ = 0 := by simp [FiniteLaw.prob]
    rw [hz,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hSk),Nat.cast_zero,zero_div]

theorem fixed_size_indicator_expect (D S : Finset V) (hS : S⊆D) {k : ℕ} (hk : k≤D.card) :
    (fixedSizeLaw D k).expect (containsIndicator S)=(k.choose S.card:ℝ)/(D.card.choose S.card:ℝ) := by
  rw [← fixed_size_contains_all D S hS hk]
  unfold FiniteLaw.prob
  congr 1
  funext T
  unfold containsIndicator
  split_ifs <;> rfl

theorem fixed_size_indicator_product (D A B : Finset V) (hA : A⊆D) (hB : B⊆D)
    {k : ℕ} (hk : k≤D.card) :
    (fixedSizeLaw D k).expect (fun T => containsIndicator A T*containsIndicator B T)=
      (k.choose (A∪B).card:ℝ)/(D.card.choose (A∪B).card:ℝ) := by
  simp_rw [containsIndicator_mul]
  exact fixed_size_indicator_expect D (A∪B) (union_subset hA hB) hk

end
end Cycle12
