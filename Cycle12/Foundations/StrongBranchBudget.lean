import Cycle12.Foundations.CliquePairs
import Cycle12.Foundations.PackingOperations

/-! Exact branch-edge accounting for a strong clique immersion. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem path_start_incidence {V : Type} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hne : x ≠ y) :
    {e ∈ p.edgeSet | x ∈ e} = {s(x,p.snd)} := by
  ext e
  constructor
  · rintro ⟨he, hx⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hx
    have hw := hp.eq_snd_of_mem_edges he
    simp only [Set.mem_singleton_iff, hw]
  · intro he
    have he' : e = s(x,p.snd) := he
    subst e
    exact ⟨p.mk_start_snd_mem_edges (Walk.not_nil_of_ne hne), Sym2.mem_mk_left _ _⟩

theorem path_endpoint_incidence_ncard {V : Type} {G : SimpleGraph V} {x y v : V}
    (p : G.Walk x y) (hp : p.IsPath) (hne : x ≠ y) (hv : v = x ∨ v = y) :
    {e ∈ p.edgeSet | v ∈ e}.ncard = 1 := by
  rcases hv with rfl | rfl
  · rw [path_start_incidence p hp hne, Set.ncard_singleton]
  · have h := path_start_incidence p.reverse hp.reverse hne.symm
    rw [Walk.edgeSet_reverse] at h
    rw [h, Set.ncard_singleton]

namespace StrongCliqueImmersion
variable {V : Type} [Fintype V] {G : SimpleGraph V} {t : ℕ}

def used (M : StrongCliqueImmersion t G) : Set (Sym2 V) :=
  ⋃ p : CliquePair t, (M.route p).val.edgeSet

def residue (M : StrongCliqueImmersion t G) : SimpleGraph V := G.deleteEdges M.used

theorem used_subset (M : StrongCliqueImmersion t G) : M.used ⊆ G.edgeSet := by
  rintro e he
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp he
  exact (M.route p).val.edges_subset_edgeSet hp

theorem residue_disjoint_used (M : StrongCliqueImmersion t G) :
    Disjoint M.residue.edgeSet M.used := by
  rw [residue, SimpleGraph.edgeSet_deleteEdges]
  exact Set.disjoint_sdiff_left

theorem residue_used_cover (M : StrongCliqueImmersion t G) :
    M.residue.edgeSet ∪ M.used = G.edgeSet := by
  rw [residue, SimpleGraph.edgeSet_deleteEdges]
  exact Set.sdiff_union_of_subset M.used_subset

theorem route_incidence_ncard (M : StrongCliqueImmersion t G) (p : CliquePair t) (i : Fin t) :
    {e ∈ (M.route p).val.edgeSet | M.branch i ∈ e}.ncard =
      if i = p.1.1 ∨ i = p.1.2 then 1 else 0 := by
  split_ifs with hi
  · exact path_endpoint_incidence_ncard _ (M.route p).property
      (fun h => (ne_of_lt p.2) (M.branch.injective h))
      (hi.imp (congrArg M.branch) (congrArg M.branch))
  · have he : {e ∈ (M.route p).val.edgeSet | M.branch i ∈ e} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro e ⟨he, hi'⟩
      exact hi (M.avoids p i (Walk.mem_support_of_mem_edges he hi'))
    rw [he, Set.ncard_empty]

/-- Each branch uses exactly one edge for each other branch. -/
theorem branch_used_edges (M : StrongCliqueImmersion t G) (i : Fin t) :
    {e ∈ M.used | M.branch i ∈ e}.ncard = t - 1 := by
  classical
  have heq : {e ∈ M.used | M.branch i ∈ e} =
      ⋃ p : CliquePair t, {e ∈ (M.route p).val.edgeSet | M.branch i ∈ e} := by
    ext e
    simp only [used, Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [heq, ncard_iUnion_disjoint]
  · simp_rw [M.route_incidence_ncard]
    have hsum : (∑ p : CliquePair t, if i = p.1.1 ∨ i = p.1.2 then 1 else 0) =
        {p : CliquePair t | i = p.1.1 ∨ i = p.1.2}.ncard := by
      rw [Set.ncard_eq_toFinset_card']
      simp only [Set.toFinset_ofPred, Finset.sum_boole, Nat.cast_id]
    rw [hsum, CliquePair.ncard_incident]
  · intro p q hpq
    exact (M.disjoint hpq).mono (fun _ h => h.1) (fun _ h => h.1)

theorem branch_degree_balance (M : StrongCliqueImmersion t G) (i : Fin t) :
    M.residue.degree (M.branch i) + (t - 1) = G.degree (M.branch i) := by
  classical
  have hnew : M.residue.incidenceSet (M.branch i) = G.incidenceSet (M.branch i) \ M.used := by
    ext e
    simp only [SimpleGraph.incidenceSet, residue, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_ofPred_eq, Set.mem_sdiff]
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

theorem branch_residual_degree {D T : ℝ} (M : StrongCliqueImmersion t G)
    (hdeg : ∀ i : Fin t, D ≤ (G.degree (M.branch i) : ℝ)) (ht : (t : ℝ) ≤ T)
    (i : Fin t) : D - T ≤ (M.residue.degree (M.branch i) : ℝ) := by
  have h := M.branch_degree_balance i
  have hR : (M.residue.degree (M.branch i) : ℝ) + (t - 1 : ℕ) = G.degree (M.branch i) := by
    exact_mod_cast h
  have hsub : ((t - 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast Nat.sub_le t 1
  have ht' : ((t - 1 : ℕ) : ℝ) ≤ T := hsub.trans ht
  have hd := hdeg i
  linarith

end StrongCliqueImmersion
end
end Cycle13
