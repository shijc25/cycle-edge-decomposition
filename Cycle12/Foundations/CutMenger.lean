import Cycle12.Foundations.GraphBranchCut
import MengerHamilton.Menger

/-! Edge-disjoint paths from explicit cut-size inequalities. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vertex side reachable after deleting `D` has all its original
boundary edges in `D`. -/
theorem reachable_cut_subset (G : SimpleGraph V) (D : Set (Sym2 V)) (u : V) :
    (cutGraph G ({w | (G.deleteEdges D).Reachable u w} : Set V).toFinset).edgeSet ⊆ D := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    change G.Adj x y ∧ _ at he
    rcases he with ⟨hxy, hside | hside⟩
    · have hx : (G.deleteEdges D).Reachable u x := by simpa using hside.1
      have hy : ¬ (G.deleteEdges D).Reachable u y := by simpa using hside.2
      by_contra hD
      have ha : (G.deleteEdges D).Adj x y := by
        rw [deleteEdges_adj]
        exact ⟨hxy, hD⟩
      exact hy (hx.trans ha.reachable)
    · have hy : (G.deleteEdges D).Reachable u y := by simpa using hside.2
      have hx : ¬ (G.deleteEdges D).Reachable u x := by simpa using hside.1
      by_contra hD
      apply hx
      apply hy.trans
      exact (show (G.deleteEdges D).Adj x y by
        rw [deleteEdges_adj]
        exact ⟨hxy, hD⟩).symm.reachable

theorem edge_reachable_of_cut_bound (G : SimpleGraph V) (k : ℕ) (u v : V)
    (hcut : ∀ S : Finset V, u ∈ S → v ∉ S → k ≤ cutSize G S) :
    G.IsEdgeReachable k u v := by
  intro D hD
  by_contra hv
  let S := ({w | (G.deleteEdges D).Reachable u w} : Set V).toFinset
  have huS : u ∈ S := by simp [S]
  have hvS : v ∉ S := by simpa [S] using hv
  have hk := hcut S huS hvS
  have hsub := reachable_cut_subset G D u
  have hsize : cutSize G S ≤ D.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcard : (D.ncard : ℕ∞) = D.encard := (Set.toFinite _).cast_ncard_eq
  have : (k : ℕ∞) ≤ D.encard := by
    rw [← hcard]
    exact_mod_cast hk.trans hsize
  exact (not_lt_of_ge this) hD

/-- A cut certificate produces actual simple paths with pairwise disjoint
original edge lists. -/
theorem disjoint_paths_of_cut_bound (G : SimpleGraph V) (k : ℕ) (u v : V)
    (hcut : ∀ S : Finset V, u ∈ S → v ∉ S → k ≤ cutSize G S) :
    ∃ p : Fin k → G.Walk u v, (∀ i, (p i).IsPath) ∧
      ∀ i j, i ≠ j → Disjoint (p i).edgeSet (p j).edgeSet := by
  obtain ⟨p, hp, hd⟩ := (Menger.isEdgeReachable_iff G k u v).mp
    (edge_reachable_of_cut_bound G k u v hcut)
  refine ⟨p, hp, fun i j hij => Set.disjoint_left.mpr ?_⟩
  intro e hi hj
  exact hd i j hij hi hj

end
end Cycle13
