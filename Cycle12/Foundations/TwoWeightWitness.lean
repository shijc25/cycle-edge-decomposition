import Cycle12.Foundations.FiniteJointLaw

namespace Cycle13.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

theorem prob_good_two_weights (μ : FiniteLaw Ω) (X Y : Ω→ℝ) (bad : Ω→Prop)
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    1-μ.expect X/s-μ.expect Y/t-μ.prob bad ≤
      μ.prob (fun ω => X ω ≤ s ∧ Y ω ≤ t ∧ ¬bad ω) := by
  have hg := μ.prob_good_weight X (fun ω => t < Y ω ∨ bad ω) hX hs
  simp only [not_or,not_lt] at hg
  have hu := μ.prob_union_le (fun ω => t < Y ω) bad
  have hm := μ.prob_gt_le_expect_div Y hY ht
  linarith

end
end Cycle13.FiniteLaw
