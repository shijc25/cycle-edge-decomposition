import Cycle12.Foundations.GraphParity

namespace Cycle13
open SimpleGraph Finset
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Toggle tree paths to prescribe the degree parity at every vertex except
one root. All selected edges stay inside the original tree. -/
theorem exists_rooted_parity_subgraph (T : SimpleGraph V) (hT : T.Connected)
    (root : V) (S : Finset V) (hroot : root ∉ S) :
    ∃ F : SimpleGraph V, F ≤ T ∧
      ∀ v : V, v ≠ root → (Even (F.degree v) ↔ v ∉ S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⊥, bot_le, ?_⟩
    intro v _
    simp
  | @insert u S hu ih =>
    have hrS : root ∉ S := fun h => hroot (mem_insert_of_mem h)
    have hru : root ≠ u := fun he => hroot (he ▸ mem_insert_self _ _)
    obtain ⟨F, hF, hpar⟩ := ih hrS
    obtain ⟨p, hp⟩ := (hT.preconnected root u).exists_isPath
    refine ⟨F ∆ walkEdgeGraph p, symmDiff_le_sup.trans (sup_le hF (walkEdgeGraph_le p)), ?_⟩
    intro v hv
    rw [graph_symmDiff_degree_even, hpar v hv, path_edge_graph_even_degree p hp hru v]
    by_cases hvu : v = u
    · subst v
      simp [hu]
    · simp [hv, hvu]

/-- Every connected finite graph loses at most a spanning forest when its
remaining degrees are made odd away from one root. -/
theorem exists_odd_remainder_forest (G : SimpleGraph V) (hG : G.Connected) (root : V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeSet.ncard ≤ Fintype.card V - componentCount G ∧
      ∀ v : V, v ≠ root → Odd ((G \ F).degree v) := by
  classical
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  let S : Finset V := univ.filter (fun v => v ≠ root ∧ Even (G.degree v))
  have hr : root ∉ S := by simp [S]
  obtain ⟨F, hFT, hpar⟩ := exists_rooted_parity_subgraph T hT.connected root S hr
  have hFG : F ≤ G := hFT.trans hTG
  have hacyc : F.IsAcyclic := hT.isAcyclic.anti hFT
  have hsize := forest_subgraph_edge_bound G F hFG hacyc
  refine ⟨F, hFG, hacyc, ?_, ?_⟩
  · simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hsize
  · intro v hv
    have hFp := hpar v hv
    have he : v ∉ S ↔ ¬Even (G.degree v) := by simp [S, hv]
    rw [he] at hFp
    apply Nat.not_even_iff_odd.mp
    intro hbad
    have hxor : G ∆ F = G \ F := symmDiff_of_ge hFG
    have hbad' : Even ((G ∆ F).degree v) := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hbad ⊢
      simpa only [hxor] using hbad
    rw [graph_symmDiff_degree_even] at hbad'
    tauto

end
end Cycle13
