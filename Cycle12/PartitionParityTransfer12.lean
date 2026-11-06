import Cycle12.LayerRemainder

namespace Cycle12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem edgeOccurrences_subgraph_split {I : Type} (L : List I)
    (G F : I → SimpleGraph V) (hF : ∀ i∈L, F i≤G i) (x y : V) :
    edgeOccurrences (L.map G) x y =
      edgeOccurrences (L.map F) x y+edgeOccurrences (L.map (fun i => G i\F i)) x y := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := hF i (by simp)
    have ht := ih (fun j hj => hF j (by simp [hj]))
    simp only [List.map_cons,edgeOccurrences_cons,ht]
    by_cases hf : (F i).Adj x y
    · have hg := hi hf
      have hd : ¬(G i\F i).Adj x y := fun h => h.2 hf
      simp only [if_pos hg,if_pos hf,if_neg hd]
      omega
    · have hd : (G i\F i).Adj x y ↔ (G i).Adj x y :=
        ⟨fun h => h.1,fun h => ⟨h,hf⟩⟩
      simp only [if_neg hf,hd]
      omega

/-- Move arbitrary subgraphs of partition pieces into the actual remainder.
Every edge still has multiplicity exactly one. -/
theorem partition_transfer_subgraphs {I : Type} (L : List I)
    (G F : I → SimpleGraph V) (H K : SimpleGraph V)
    (hF : ∀ i∈L, F i≤G i) (hp : GraphPartition H (K::L.map G)) :
    GraphPartition H ((K⊔graphUnion (L.map F))::L.map (fun i => G i\F i)) := by
  intro x y
  have hh := hp x y
  rw [edgeOccurrences_cons,edgeOccurrences_subgraph_split L G F hF x y] at hh
  simp only [edgeOccurrences_cons,SimpleGraph.sup_adj,←edgeOccurrences_pos]
  by_cases hk : K.Adj x y <;>
    by_cases hf : 0<edgeOccurrences (L.map F) x y <;>
    by_cases hg : H.Adj x y <;> simp_all <;> omega

theorem transferred_remainder_supported {I : Type} (L : List I)
    (F : I → SimpleGraph V) (K : SimpleGraph V) (A : Finset V)
    (hK : SupportedOn K A) (hF : ∀ i∈L, SupportedOn (F i) A) :
    SupportedOn (K⊔graphUnion (L.map F)) A := by
  intro x y h
  rcases h with h | h
  · exact hK h
  · obtain ⟨G,hG,hxy⟩ := (graphUnion_adj _ _ _).mp h
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hG
    exact hF i hi hxy

theorem transferred_remainder_edge_count (L : List (AssignedPiece V))
    (F : AssignedPiece V → SimpleGraph V) (K : SimpleGraph V) (A : Finset V)
    (hd : L.Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (hA : ∀ P∈L, P.vertices⊆A) (hF : ∀ P∈L, edgeCount (F P)≤P.vertices.card) :
    edgeCount (K⊔graphUnion (L.map F))≤edgeCount K+A.card := by
  have hsum : ((L.map F).map edgeCount).sum ≤ (L.map (fun P => P.vertices.card)).sum := by
    rw [List.map_map]
    exact List.sum_le_sum (by intro P hP; exact hF P hP)
  have hc := list_disjoint_card_le (L.map AssignedPiece.vertices) A
    (List.pairwise_map.mpr hd) (by
      intro B hB
      obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hB
      exact hA P hP)
  simp only [List.map_map,Function.comp_def] at hc
  exact (edgeCount_sup_le _ _).trans
    (Nat.add_le_add_left ((edgeCount_union_le _).trans (hsum.trans hc)) _)

theorem parity_remainder_cost {h L N E E' : ℝ}
    (hh : 2000≤h) (hN : 0≤N) (hE : 2*E≤h*(1+log (L/h)/log 2)*N)
    (hF : E'≤E+N) :
    2*E'≤h*((1001/1000:ℝ)+log (L/h)/log 2)*N := by
  nlinarith only [hE,hF,mul_nonneg (show 0≤h-2000 by linarith) hN]

end
end Cycle12
