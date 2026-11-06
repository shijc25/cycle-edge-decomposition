import Cycle12.FixedIntersectionDisintegration

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A subsample size may depend on the marked-neighbor count. Its marginal,
conditional on that count only, is uniform in the full neighbor set. -/
theorem fixed_intersection_adaptive_subsample (D N : Finset V) (hN : N⊆D)
    {k : ℕ} (hk : k ≤ D.card) (r : ℕ → ℕ) (hr : ∀ j, r j ≤ j)
    (f : Finset V → ℝ) :
    (fixedSizeLaw D k).expect (fun T =>
        (fixedSizeLaw (T∩N) (r (T∩N).card)).expect f)=
      (fixedSizeLaw D k).expect (fun T =>
        (fixedSizeLaw N (r (T∩N).card)).expect f) := by
  rw [fixed_intersection_disintegration D N hN hk
      (fun S => (fixedSizeLaw S (r S.card)).expect f),
    fixed_intersection_disintegration D N hN hk
      (fun S => (fixedSizeLaw N (r S.card)).expect f)]
  apply sum_congr rfl
  intro j hj
  have hjN : j ≤ N.card := by have hh := mem_range.mp hj; omega
  congr 1
  calc
    _ = (fixedSizeLaw N j).expect (fun S => (fixedSizeLaw S (r j)).expect f) := by
      apply finite_expect_congr_support
      intro S hS
      rw [(fixed_size_support N S hjN hS).2]
    _ = (fixedSizeLaw N (r j)).expect f := fixed_subsample_expect N hjN (hr j) f
    _ = (fixedSizeLaw N j).expect (fun S => (fixedSizeLaw N (r S.card)).expect f) := by
      rw [← (fixedSizeLaw N j).expect_const ((fixedSizeLaw N (r j)).expect f)]
      apply finite_expect_congr_support
      intro S hS
      rw [(fixed_size_support N S hjN hS).2]

end
end Cycle12
