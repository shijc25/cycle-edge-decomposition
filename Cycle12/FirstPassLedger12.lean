import Cycle12.ReserveGeometry12
import Cycle12.PackingParity12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Delete the reserved and internal edges before forming the first-pass
exterior graph. A is the union of the first two vertex reservoirs. -/
def firstExterior (G R : SimpleGraph V) (A U : Finset V) : SimpleGraph (Aᶜ : Set V) :=
  (G.deleteEdges (R.edgeSet ∪ (insideGraph G U).edgeSet)).induce (Aᶜ : Set V)

def firstExteriorHom (G R : SimpleGraph V) (A U : Finset V) : firstExterior G R A U →g G where
  toFun := Subtype.val
  map_rel' := by
    intro x y h
    exact (deleteEdges_adj.mp h).1

/-- Once all first-pass exterior edges are covered, every remaining
unreserved, noninternal edge goes between A and the outside of U. -/
theorem first_pass_bipartite {G R : SimpleGraph V} (A U : Finset V) (hAU : A ⊆ U)
    (P : CyclePacking G)
    (hcover : Sym2.map (firstExteriorHom G R A U) '' (firstExterior G R A U).edgeSet ⊆ P.used)
    {x y : V} (hxy : (P.residue.deleteEdges (R.edgeSet ∪ (insideGraph G U).edgeSet)).Adj x y) :
    (x ∈ A ∧ y ∉ U) ∨ (y ∈ A ∧ x ∉ U) := by
  obtain ⟨hP,hrest⟩ := deleteEdges_adj.mp hxy
  obtain ⟨hG,hnot⟩ := deleteEdges_adj.mp hP
  by_cases hx : x ∈ A
  · refine Or.inl ⟨hx,fun hy => ?_⟩
    exact hrest (Or.inr ⟨hG,hAU hx,hy⟩)
  · by_cases hy : y ∈ A
    · refine Or.inr ⟨hy,fun hxU => ?_⟩
      exact hrest (Or.inr ⟨hG,hxU,hAU hy⟩)
    · exfalso
      apply hnot
      apply hcover
      let xx : (Aᶜ : Set V) := ⟨x,by simpa using hx⟩
      let yy : (Aᶜ : Set V) := ⟨y,by simpa using hy⟩
      refine ⟨s(xx,yy),?_,rfl⟩
      exact deleteEdges_adj.mpr ⟨hG,hrest⟩

/-- At a vertex outside U, internal-edge deletion has no degree cost.
The reserve is an actual subgraph, so its degree is subtracted exactly. -/
theorem delete_reserve_degree (G R T : SimpleGraph V) (hR : R ≤ G) (v : V)
    (hT : ∀ w, ¬T.Adj v w) :
    (G.deleteEdges (R.edgeSet ∪ T.edgeSet)).degree v + R.degree v = G.degree v := by
  have hn : (G.deleteEdges (R.edgeSet ∪ T.edgeSet)).neighborFinset v =
      G.neighborFinset v \ R.neighborFinset v := by
    ext w
    rw [(G.deleteEdges (R.edgeSet ∪ T.edgeSet)).mem_neighborFinset,
      Finset.mem_sdiff,G.mem_neighborFinset,R.mem_neighborFinset,deleteEdges_adj]
    change (G.Adj v w ∧ ¬(R.Adj v w ∨ T.Adj v w)) ↔ _
    simp only [hT w,or_false]
  have hs : R.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).mpr (hR ((R.mem_neighborFinset v w).mp hw))
  rw [←card_neighborFinset_eq_degree,hn,←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  exact Finset.card_sdiff_add_card_eq_card hs

theorem even_first_pass_outside_odd {G R : SimpleGraph V} (U : Finset V)
    (P : CyclePacking G) (hR : R ≤ P.residue) (heven : ∀ v, Even (G.degree v))
    (v : V) (hv : v ∉ U) (hRv : R.degree v = 1) :
    Odd ((P.residue.deleteEdges (R.edgeSet ∪ (insideGraph G U).edgeSet)).degree v) := by
  have hp := (packing_residue_parity P v).mpr (heven v)
  have hd := delete_reserve_degree P.residue R (insideGraph G U) hR v
    (fun w h => hv h.2.1)
  rw [hRv] at hd
  simp only [Nat.even_iff] at hp
  rw [Nat.odd_iff]
  omega

end
end Cycle12
