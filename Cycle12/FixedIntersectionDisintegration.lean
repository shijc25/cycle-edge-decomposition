import Cycle12.FixedIntersectionConditioning

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

theorem finite_expect_congr_support {Ω : Type} [Fintype Ω] (mu : FiniteLaw Ω)
    {f g : Ω → ℝ} (h : ∀ x, 0 < mu.mass x → f x=g x) : mu.expect f=mu.expect g := by
  exact le_antisymm (mu.expect_mono_support (fun x hx => (h x hx).le))
    (mu.expect_mono_support (fun x hx => (h x hx).symm.le))

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Full disintegration by the exact intersection size. The range is capped
at both the sample and neighbor-set sizes, so each inner law is truly uniform
at the stated size and never invokes the total-law cap. -/
theorem fixed_intersection_disintegration (D B : Finset V) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) (f : Finset V → ℝ) :
    (fixedSizeLaw D k).expect (fun T => f (T∩B))=
      ∑ j∈range (min k B.card+1),
        (fixedSizeLaw D k).prob (fun T => (T∩B).card=j)*(fixedSizeLaw B j).expect f := by
  have he : (fixedSizeLaw D k).expect (fun T => f (T∩B))=
      (fixedSizeLaw D k).expect (fun T => ∑ j∈range (min k B.card+1),
        if (T∩B).card=j then f (T∩B) else 0) := by
    apply finite_expect_congr_support
    intro T hT
    have hTk := (fixed_size_support D T hk hT).2
    have hjk : (T∩B).card ≤ k := by
      rw [← hTk]
      exact card_le_card inter_subset_left
    have hjB : (T∩B).card ≤ B.card := card_le_card inter_subset_right
    have hj : (T∩B).card∈range (min k B.card+1) := mem_range.mpr (by omega)
    rw [sum_eq_single (T∩B).card]
    · simp
    · intro j _ hne
      exact if_neg (Ne.symm hne)
    · exact fun h => (h hj).elim
  rw [he,FiniteLaw.expect_finset_sum]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  exact fixed_intersection_conditioned_expect D B hB hk (by omega) (by omega) f

end
end Cycle12
