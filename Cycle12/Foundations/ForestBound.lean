import Cycle12.Foundations.Definitions

/-! The exact `n-c(G)` bound for an acyclic spanning subgraph. -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
universe u
variable {V : Type u} [Fintype V]
attribute [local instance] Classical.propDecidable

def componentVertexEquiv (G : SimpleGraph V) :
    (Σ c : G.ConnectedComponent, c) ≃ V where
  toFun x := x.2.1
  invFun v := ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv := by
    rintro ⟨c, v, hv⟩
    change G.connectedComponentMk v = c at hv
    cases hv
    rfl
  right_inv _ := rfl

theorem sum_component_vertices (G : SimpleGraph V) :
    ∑ c : G.ConnectedComponent, Fintype.card c = Fintype.card V := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (componentVertexEquiv G)

theorem component_degree_eq (G : SimpleGraph V) (c : G.ConnectedComponent) (v : c) :
    c.toSimpleGraph.degree v = G.degree v.1 := by
  classical
  let e : c.toSimpleGraph.neighborSet v ≃ G.neighborSet v.1 :=
    { toFun := fun w => ⟨w.1.1, w.2⟩
      invFun := fun w => ⟨⟨w.1, c.mem_supp_of_adj_mem_supp v.2 w.2⟩, w.2⟩
      left_inv := fun w => Subtype.ext (Subtype.ext rfl)
      right_inv := fun w => Subtype.ext rfl }
  calc
    _ = Fintype.card (c.toSimpleGraph.neighborSet v) :=
      (c.toSimpleGraph.card_neighborSet_eq_degree v).symm
    _ = Fintype.card (G.neighborSet v.1) := Fintype.card_congr e
    _ = _ := G.card_neighborSet_eq_degree v.1

theorem sum_component_edges (G : SimpleGraph V) :
    ∑ c : G.ConnectedComponent, c.toSimpleGraph.edgeFinset.card = G.edgeFinset.card := by
  have hsum : ∑ c : G.ConnectedComponent, ∑ v : c, G.degree v.1 = ∑ v : V, G.degree v := by
    calc
      _ = ∑ x : (Σ c : G.ConnectedComponent, c), G.degree x.2.1 :=
        (Fintype.sum_sigma (fun x : (Σ c : G.ConnectedComponent, c) => G.degree x.2.1)).symm
      _ = _ := (componentVertexEquiv G).sum_comp (fun v => G.degree v)
  have hlocal : ∀ c : G.ConnectedComponent,
      2 * c.toSimpleGraph.edgeFinset.card = ∑ v : c, G.degree v.1 := by
    intro c
    rw [← c.toSimpleGraph.sum_degrees_eq_twice_card_edges]
    apply sum_congr rfl
    intro v _
    exact component_degree_eq G c v
  have ht : 2 * (∑ c : G.ConnectedComponent, c.toSimpleGraph.edgeFinset.card) =
      2 * G.edgeFinset.card := by
    rw [mul_sum]
    simp_rw [hlocal]
    rw [hsum, G.sum_degrees_eq_twice_card_edges]
  omega

theorem forest_edges_add_components (G : SimpleGraph V) (hforest : G.IsAcyclic) :
    G.edgeFinset.card + componentCount G = Fintype.card V := by
  have hlocal : ∀ c : G.ConnectedComponent,
      c.toSimpleGraph.edgeFinset.card + 1 = Fintype.card c :=
    fun c => (hforest.isTree_connectedComponent c).card_edgeFinset
  have hsum := congrArg (fun f : G.ConnectedComponent → ℕ => ∑ c, f c) (funext hlocal)
  simpa only [sum_add_distrib, sum_component_edges, sum_const, card_univ,
    smul_eq_mul, mul_one, sum_component_vertices, componentCount, Nat.card_eq_fintype_card]
      using hsum

theorem forest_subgraph_edge_bound (G F : SimpleGraph V)
    (hsub : F ≤ G) (hforest : F.IsAcyclic) :
    F.edgeFinset.card ≤ Fintype.card V - componentCount G := by
  have hF := forest_edges_add_components F hforest
  have hc : componentCount G ≤ componentCount F :=
    ConnectedComponent.card_le_card_of_le hsub
  omega

end
end Cycle13
