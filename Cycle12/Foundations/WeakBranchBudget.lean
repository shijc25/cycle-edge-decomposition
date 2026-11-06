import Cycle12.Foundations.WeakImmersionRouting
import Cycle12.Foundations.StrongBranchBudget

/-! Exact branch use for weak models, counting both edges at every internal
visit. This does not assert existence of a model with few such visits. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}

lemma path_internal_incidence_ncard {x y v : V} (p : G.Walk x y) (hp : p.IsPath)
    (hv : v ∈ p.support) (hvx : v ≠ x) (hvy : v ≠ y) :
    {e ∈ p.edgeSet | v ∈ e}.ncard = 2 := by
  let A := {e ∈ (p.takeUntil v hv).edgeSet | v ∈ e}
  let B := {e ∈ (p.dropUntil v hv).edgeSet | v ∈ e}
  have he : {e ∈ p.edgeSet | v ∈ e} = A ∪ B := by
    conv_lhs => rw [← p.take_spec hv]
    ext e
    simp only [A, B, Walk.edgeSet_append, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro e heA heB
    exact hp.isTrail.disjoint_edges_takeUntil_dropUntil hv heA.1 heB.1
  have hA : A.ncard = 1 := path_endpoint_incidence_ncard _ (hp.takeUntil hv) hvx.symm (Or.inr rfl)
  have hB : B.ncard = 1 := path_endpoint_incidence_ncard _ (hp.dropUntil hv) hvy (Or.inl rfl)
  rw [he, Set.ncard_union_eq hd, hA, hB]

namespace WeakCliqueImmersion
variable {t : ℕ}

def internalVisits (M : WeakCliqueImmersion t G) (i : Fin t) : Finset (CliquePair t) :=
  univ.filter (fun p => ¬ (i = p.1.1 ∨ i = p.1.2) ∧ M.branch i ∈ (M.route p).val.support)

theorem route_incidence_ncard (M : WeakCliqueImmersion t G) (p : CliquePair t) (i : Fin t) :
    {e ∈ (M.route p).val.edgeSet | M.branch i ∈ e}.ncard =
      if i = p.1.1 ∨ i = p.1.2 then 1
      else if M.branch i ∈ (M.route p).val.support then 2 else 0 := by
  split_ifs with hi hv
  · exact path_endpoint_incidence_ncard _ (M.route p).property
      (fun h => (ne_of_lt p.2) (M.branch.injective h))
      (hi.imp (congrArg M.branch) (congrArg M.branch))
  · exact path_internal_incidence_ncard _ (M.route p).property hv
      (fun h => hi (Or.inl (M.branch.injective h)))
      (fun h => hi (Or.inr (M.branch.injective h)))
  · have he : {e ∈ (M.route p).val.edgeSet | M.branch i ∈ e} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro e ⟨he, hie⟩
      exact hv (Walk.mem_support_of_mem_edges he hie)
    rw [he, Set.ncard_empty]

/-- Weak branch usage is the endpoint contribution `t-1` plus exactly two
edges for each occurrence as the interior of another immersion path. -/
theorem branch_used_edges (M : WeakCliqueImmersion t G) (i : Fin t) :
    {e ∈ M.used | M.branch i ∈ e}.ncard = (t-1) + 2*(M.internalVisits i).card := by
  have he : {e ∈ M.used | M.branch i ∈ e} =
      ⋃ p : CliquePair t, {e ∈ (M.route p).val.edgeSet | M.branch i ∈ e} := by
    ext e
    simp only [used, Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  rw [he, ncard_iUnion_disjoint]
  · simp_rw [M.route_incidence_ncard]
    have hecount : (∑ p : CliquePair t, if i = p.1.1 ∨ i = p.1.2 then 1 else 0) = t-1 := by
      rw [← CliquePair.ncard_incident i, Set.ncard_eq_toFinset_card']
      simp only [Set.toFinset_ofPred, sum_boole, Nat.cast_id]
    have hvcount : (∑ p : CliquePair t,
        if ¬ (i = p.1.1 ∨ i = p.1.2) ∧ M.branch i ∈ (M.route p).val.support then 1 else 0) =
        (M.internalVisits i).card := by simp [internalVisits]
    rw [← hecount, ← hvcount, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hi : i = p.1.1 ∨ i = p.1.2 <;>
      by_cases hv : M.branch i ∈ (M.route p).val.support <;> simp [hi, hv]
  · intro p q hpq
    exact (M.disjoint hpq).mono (fun _ h => h.1) (fun _ h => h.1)

theorem branch_degree_balance (M : WeakCliqueImmersion t G) (i : Fin t) :
    M.residue.degree (M.branch i) + (t-1) + 2*(M.internalVisits i).card =
      G.degree (M.branch i) := by
  have hnew : M.residue.incidenceSet (M.branch i) = G.incidenceSet (M.branch i) \ M.used := by
    ext e
    simp only [SimpleGraph.incidenceSet, residue, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_setOf_eq, Set.mem_sdiff]
    tauto
  have hused : G.incidenceSet (M.branch i) ∩ M.used = {e ∈ M.used | M.branch i ∈ e} := by
    ext e
    constructor
    · rintro ⟨⟨_, hi⟩, hu⟩
      exact ⟨hu, hi⟩
    · rintro ⟨hu, hi⟩
      exact ⟨⟨M.used_subset hu, hi⟩, hu⟩
  have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.incidenceSet (M.branch i)) M.used
  rw [hused, M.branch_used_edges, ← hnew, SimpleGraph.ncard_incidenceSet,
    SimpleGraph.ncard_incidenceSet] at h
  omega

/-- The 11t/10 target is equivalent to an explicit bound on internal
visits. Existence of such a model remains a separate combinatorial task. -/
theorem branch_budget_of_internal_visits (M : WeakCliqueImmersion t G) (i : Fin t)
    (hv : 20*(M.internalVisits i).card ≤ t+10) :
    10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*t := by
  rw [M.branch_used_edges]
  have hi := i.isLt
  omega

end WeakCliqueImmersion
end
end Cycle13
