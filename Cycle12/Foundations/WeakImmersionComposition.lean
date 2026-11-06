import Cycle12.Foundations.WeakBranchBudget
import Cycle12.Foundations.ImmersionMap

/-! Strong immersion of a host graph preserves an upper bound on every
branch's total used edges, even when the clique model itself is weak. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace WeakCliqueImmersion
variable {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W} {t : ℕ}

def lift (M : WeakCliqueImmersion t H) (R : EdgeRouting H G) :
    WeakCliqueImmersion t G := by
  classical
  refine {
    branch := M.branch.trans R.vertex
    route := fun p => (R.liftWalk (M.route p).val).toPath
    disjoint := ?_ }
  intro p q hpq
  exact (R.liftWalk_disjoint _ _ (M.disjoint hpq)).mono
    (R.liftWalk (M.route p).val).edges_toPath_subset_edges
    (R.liftWalk (M.route q).val).edges_toPath_subset_edges

theorem lift_internalVisits_subset [Fintype V] [Fintype W]
    (M : WeakCliqueImmersion t H) (R : EdgeRouting H G) (i : Fin t) :
    (M.lift R).internalVisits i ⊆ M.internalVisits i := by
  intro p hp
  simp only [internalVisits, mem_filter, mem_univ, true_and] at hp ⊢
  refine ⟨hp.1, ?_⟩
  exact R.liftWalk_support _ (M.branch i)
    ((R.liftWalk (M.route p).val).support_toPath_subset_support hp.2)

/-- Loop erasure can remove internal branch visits, and cannot create any. -/
theorem lift_branch_used_le [Fintype V] [Fintype W]
    (M : WeakCliqueImmersion t H) (R : EdgeRouting H G) (i : Fin t) :
    {e ∈ (M.lift R).used | (M.lift R).branch i ∈ e}.ncard ≤
      {e ∈ M.used | M.branch i ∈ e}.ncard := by
  rw [(M.lift R).branch_used_edges, M.branch_used_edges]
  have hc := card_le_card (M.lift_internalVisits_subset R i)
  omega

theorem lift_preserves_branch_budget [Fintype V] [Fintype W]
    (M : WeakCliqueImmersion t H) (R : EdgeRouting H G) {L : ℕ}
    (hbudget : ∀ i, 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ L) :
    ∀ i, 10*{e ∈ (M.lift R).used | (M.lift R).branch i ∈ e}.ncard ≤ L := by
  intro i
  exact (Nat.mul_le_mul_left 10 (M.lift_branch_used_le R i)).trans (hbudget i)

end WeakCliqueImmersion
end
end Cycle13
