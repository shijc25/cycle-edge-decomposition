import Cycle12.Foundations.ForestBound
import Cycle12.Foundations.UpstreamBridge

/-! Assemble exact edge decompositions over connected components. -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
variable {V : Type} [Fintype V]
attribute [local instance] Classical.propDecidable

theorem component_edge_image (G : SimpleGraph V) (c : G.ConnectedComponent) :
    Sym2.map c.toSimpleGraph_hom '' c.toSimpleGraph.edgeSet =
      c.toSimpleGraph.spanningCoe.edgeSet := by
  exact (c.toSimpleGraph.edgeSet_map (Function.Embedding.subtype (· ∈ c))).symm

theorem component_edges_disjoint (G : SimpleGraph V) :
    Pairwise (fun c d : G.ConnectedComponent =>
      Disjoint (Sym2.map c.toSimpleGraph_hom '' c.toSimpleGraph.edgeSet)
        (Sym2.map d.toSimpleGraph_hom '' d.toSimpleGraph.edgeSet)) := by
  intro c d hcd
  rw [component_edge_image, component_edge_image]
  apply Set.disjoint_left.mpr
  intro e hec hed
  induction e using Sym2.ind with
  | _ u v =>
    have hc := (c.adj_spanningCoe_toSimpleGraph).mp hec
    have hd := (d.adj_spanningCoe_toSimpleGraph).mp hed
    exact hcd (ConnectedComponent.eq_of_common_vertex hc.1 hd.1)

theorem component_edges_cover (G : SimpleGraph V) :
    (⋃ c : G.ConnectedComponent, Sym2.map c.toSimpleGraph_hom '' c.toSimpleGraph.edgeSet) =
      G.edgeSet := by
  simp only [component_edge_image]
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    constructor
    · intro he
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp he
      exact (c.adj_spanningCoe_toSimpleGraph).mp hc |>.2
    · intro he
      apply Set.mem_iUnion.mpr
      exact ⟨G.connectedComponentMk u,
        (G.connectedComponentMk u).adj_spanningCoe_toSimpleGraph.mpr ⟨rfl, he⟩⟩

theorem decomposition_from_components (G : SimpleGraph V)
    (k : G.ConnectedComponent → ℕ)
    (hk : ∀ c, EdgeDecomposition c.toSimpleGraph (k c)) :
    EdgeDecomposition G (∑ c, k c) := by
  exact OAI.ErdosGallai.edgeDecomposition_assemble G (fun c : G.ConnectedComponent => c)
    (fun c => c.toSimpleGraph) (fun c => c.toSimpleGraph_hom)
    (fun _ => Subtype.val_injective) (component_edges_disjoint G)
    (component_edges_cover G) k hk

theorem sum_component_ranks (G : SimpleGraph V) :
    ∑ c : G.ConnectedComponent, (Fintype.card c - 1) =
      Fintype.card V - componentCount G := by
  have hlocal : ∀ c : G.ConnectedComponent,
      (Fintype.card c - 1) + 1 = Fintype.card c := by
    intro c
    have : Nonempty c := ⟨⟨c.nonempty_supp.some, c.nonempty_supp.some_mem⟩⟩
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
  have hsum := congrArg (fun f : G.ConnectedComponent → ℕ => ∑ c, f c) (funext hlocal)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one,
    sum_component_vertices] at hsum
  have hc : componentCount G = Fintype.card G.ConnectedComponent := Nat.card_eq_fintype_card
  omega

/-- Passing from the connected `n-1` bound to the exact general `n-c(G)` bound. -/
theorem coefficient13_of_component_bounds (G : SimpleGraph V)
    (h : ∀ c : G.ConnectedComponent, ∃ k, EdgeDecomposition c.toSimpleGraph k ∧
      k ≤ 13 * (Fintype.card c - 1)) :
    ∃ k, EdgeDecomposition G k ∧ k ≤ 13 * (Fintype.card V - componentCount G) := by
  choose k hdec hbound using h
  refine ⟨∑ c, k c, decomposition_from_components G k hdec, ?_⟩
  calc
    _ ≤ ∑ c : G.ConnectedComponent, 13 * (Fintype.card c - 1) :=
      sum_le_sum (fun c _ => hbound c)
    _ = _ := by rw [← mul_sum, sum_component_ranks]

end
end Cycle13
