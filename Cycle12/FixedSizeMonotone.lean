import Cycle12.FixedIntersectionDisintegration

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Actual nested uniform samples give stochastic monotonicity in size. -/
theorem fixed_size_expect_antitone (D : Finset V) {j k : ℕ}
    (hk : k≤D.card) (hjk : j≤k) (f : Finset V → ℝ) (hf : Antitone f) :
    (fixedSizeLaw D k).expect f ≤ (fixedSizeLaw D j).expect f := by
  rw [← fixed_subsample_expect D hk hjk f]
  apply FiniteLaw.expect_mono_support
  intro T hT
  have hcard := (fixed_size_support D T hk hT).2
  rw [← (fixedSizeLaw T j).expect_const (f T)]
  apply FiniteLaw.expect_mono_support
  intro S hS
  have hST := (fixed_size_support T S (by omega : j≤T.card) hS).1
  exact hf hST

theorem fixed_size_probability_antitone (D : Finset V) {j k : ℕ}
    (hk : k≤D.card) (hjk : j≤k) (E : Finset V → Prop)
    (hE : ∀ S T, S⊆T → E T → E S) :
    (fixedSizeLaw D k).prob E ≤ (fixedSizeLaw D j).prob E := by
  apply fixed_size_expect_antitone D hk hjk (fun S => if E S then 1 else 0)
  intro S T hST
  by_cases ht : E T
  · simp only [if_pos ht,if_pos (hE S T hST ht),le_refl]
  · simp only [if_neg ht]
    split_ifs <;> norm_num

theorem fixed_size_card_le_probability (D : Finset V) {j : ℕ} (hj : j≤D.card) (k : ℕ) :
    (fixedSizeLaw D j).prob (fun S => S.card≤k)=if j≤k then (1:ℝ) else 0 := by
  rw [← (fixedSizeLaw D j).expect_const (if j≤k then (1:ℝ) else 0)]
  apply finite_expect_congr_support
  intro S hS
  have hc := (fixed_size_support D S hj hS).2
  simp only [hc]

end
end Cycle12
