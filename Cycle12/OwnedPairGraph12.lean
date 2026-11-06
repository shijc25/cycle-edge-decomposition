import Cycle12.OwnedTwoEdgeFamily12

namespace Cycle12.OwnedTwoEdgeFamily12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : I → Finset V}

def graph (P : OwnedTwoEdgeFamily12 G A) : SimpleGraph V := fromEdgeSet P.used

theorem graph_edges (P : OwnedTwoEdgeFamily12 G A) : P.graph.edgeSet=P.used := by
  rw [graph,edgeSet_fromEdgeSet]
  apply Set.Subset.antisymm Set.sdiff_subset
  intro e he
  exact ⟨he,G.edgeSet_subset_compl_diagSet (P.used_subset he)⟩

theorem graph_le (P : OwnedTwoEdgeFamily12 G A) : P.graph ≤ G := by
  apply edgeSet_subset_edgeSet.mp
  rw [P.graph_edges]
  exact P.used_subset

theorem graph_adj (P : OwnedTwoEdgeFamily12 G A) (x y : V) :
    P.graph.Adj x y ↔ s(x,y)∈P.used := by
  change s(x,y)∈P.graph.edgeSet ↔ _
  rw [P.graph_edges]

theorem restrict_partition (P : OwnedTwoEdgeFamily12 G A) (keep : P.Index → Prop) :
    (P.restrict keep).used∪(P.restrict (fun j => ¬keep j)).used=P.used ∧
      Disjoint (P.restrict keep).used (P.restrict (fun j => ¬keep j)).used := by
  constructor
  · apply Set.Subset.antisymm
    · exact Set.union_subset (P.restrict_used_subset keep) (P.restrict_used_subset (fun j => ¬keep j))
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      by_cases hk : keep j
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨j,hk⟩,hj⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j,hk⟩,hj⟩)
  · apply Set.disjoint_left.mpr
    intro e he hf
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
    have hne : j.val ≠ k.val := by intro h; exact k.property (h ▸ j.property)
    exact Set.disjoint_left.mp (P.disjoint hne) hj hk

/-- Outside the core, every incident edge belongs to exactly one pair
centered at that vertex. This gives the even degree needed by completion. -/
theorem exterior_incidence (P : OwnedTwoEdgeFamily12 G A) (U : Finset V)
    (ha : ∀ j,P.left j∈U) (hb : ∀ j,P.right j∈U) (v : V) (hv : v∉U) :
    P.graph.incidenceSet v=(P.restrict (fun j => P.center j=v)).used := by
  ext e
  constructor
  · rintro ⟨he,hvE⟩
    rw [P.graph_edges] at he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hc : P.center j=v := by
      rcases hj with rfl|rfl
      · rcases Sym2.mem_iff.mp hvE with h|h
        · exact h.symm
        · exact False.elim (hv (h.symm ▸ ha j))
      · rcases Sym2.mem_iff.mp hvE with h|h
        · exact h.symm
        · exact False.elim (hv (h.symm ▸ hb j))
    exact Set.mem_iUnion.mpr ⟨⟨j,hc⟩,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨?_,?_⟩
    · rw [P.graph_edges]
      exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
    · rcases hj with rfl|rfl <;> simp only [restrict,j.property,Sym2.mem_mk_left]

theorem exterior_degree (P : OwnedTwoEdgeFamily12 G A) (U : Finset V)
    (ha : ∀ j,P.left j∈U) (hb : ∀ j,P.right j∈U) (v : V) (hv : v∉U) :
    P.graph.degree v=2*Fintype.card {j : P.Index // P.center j=v} := by
  rw [←SimpleGraph.ncard_incidenceSet,P.exterior_incidence U ha hb v hv]
  convert (P.restrict (fun j => P.center j=v)).used_card using 1 <;> congr!

theorem exterior_even (P : OwnedTwoEdgeFamily12 G A) (U : Finset V)
    (ha : ∀ j,P.left j∈U) (hb : ∀ j,P.right j∈U) (v : V) (hv : v∉U) :
    Even (P.graph.degree v) := by
  rw [P.exterior_degree U ha hb v hv]
  exact even_two_mul _

/-- Removing whole center classes preserves every incident edge at a
retained exterior center. The initial pairing need not constrain completion. -/
theorem restrict_center_incidence (P : OwnedTwoEdgeFamily12 G A) (U : Finset V)
    (ha : ∀ j,P.left j∈U) (hb : ∀ j,P.right j∈U)
    (keep : V → Prop) (v : V) (hv : v∉U) (hk : keep v) :
    (P.restrict (fun j => keep (P.center j))).graph.incidenceSet v=P.graph.incidenceSet v := by
  ext e
  constructor
  · rintro ⟨he,hvE⟩
    rw [graph_edges] at he
    refine ⟨?_,hvE⟩
    rw [P.graph_edges]
    exact P.restrict_used_subset _ he
  · intro he
    have h := he
    rw [P.exterior_incidence U ha hb v hv] at h
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
    change {j : P.Index // P.center j=v} at j
    refine ⟨?_,he.2⟩
    rw [graph_edges]
    exact Set.mem_iUnion.mpr ⟨⟨j.val,Eq.mpr (congrArg keep j.property) hk⟩,hj⟩

theorem restrict_center_degree (P : OwnedTwoEdgeFamily12 G A) (U : Finset V)
    (ha : ∀ j,P.left j∈U) (hb : ∀ j,P.right j∈U)
    (keep : V → Prop) (v : V) (hv : v∉U) (hk : keep v) :
    (P.restrict (fun j => keep (P.center j))).graph.degree v=P.graph.degree v := by
  rw [←SimpleGraph.ncard_incidenceSet,←SimpleGraph.ncard_incidenceSet,
    P.restrict_center_incidence U ha hb keep v hv hk]

end
end Cycle12.OwnedTwoEdgeFamily12
