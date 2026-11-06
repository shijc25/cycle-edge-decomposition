import Cycle12.DFSBoundarySuccessor
import Cycle12.DFSOverlap
import OAI.Combinatorics.CycleDecomposition.ScaleHierarchy

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem supported_walk_end {G : SimpleGraph V} {A : Finset V}
    (hG : SupportedOn G A) {x y : V} (p : G.Walk x y) (hx : x∈A) : y∈A := by
  induction p with
  | nil => exact hx
  | cons h p ih => exact ih (hG h).2

theorem supported_ancestorClosed {G : SimpleGraph V} {A : Finset V}
    (hG : SupportedOn G A) (F : NormalDFSForest G) : F.AncestorClosed A := by
  intro x hx y hy
  obtain ⟨p,_,_⟩ := F.exists_ancestor_path hy
  exact supported_walk_end hG p hx

def dfsAssigned {G : SimpleGraph V} {k T : ℕ} (B : DFSBlock G k T) : AssignedPiece V :=
  ⟨B.vertices,B.graph,B.supported⟩

def dfsBoxes {G : SimpleGraph V} {A : Finset V} {k T : ℕ}
    (P : DFSPartition G A k T) : List (AssignedPiece V) :=
  List.ofFn (fun i => dfsAssigned (P.block i))

theorem edgeOccurrences_ofFn {n : ℕ} (f : Fin n → SimpleGraph V) (x y : V) :
    edgeOccurrences (List.ofFn f) x y = ∑ i, if (f i).Adj x y then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,edgeOccurrences_cons,ih,Fin.sum_univ_succ]

theorem dfs_boxes_partition {G : SimpleGraph V} {A : Finset V} {k T : ℕ}
    (hG : SupportedOn G A) (P : DFSPartition G A k T) :
    GraphPartition G ((dfsBoxes P).map AssignedPiece.graph) := by
  have hu : (⋃ i, (P.block i).graph.edgeSet)=G.edgeSet := by
    rw [P.edge_union]
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      change (G.Adj x y ∧ x∈A ∧ y∈A) ↔ G.Adj x y
      exact ⟨fun h => h.1,fun h => ⟨h,hG h⟩⟩
  intro x y
  simp only [dfsBoxes,List.map_ofFn,dfsAssigned,Function.comp_def,edgeOccurrences_ofFn]
  by_cases hxy : G.Adj x y
  · rw [if_pos hxy]
    have hm : s(x,y)∈⋃ i, (P.block i).graph.edgeSet := hu.symm ▸ hxy
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hm
    rw [Finset.sum_eq_single i]
    · exact if_pos hi
    · intro j _ hji
      apply if_neg
      intro hj
      exact Set.disjoint_left.mp (P.edge_disjoint hji) hj hi
    · simp
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (fun h => hxy ((P.block i).graph_le h))

theorem dfs_boxes_mass {G : SimpleGraph V} {A : Finset V} {k T : ℕ}
    (hk : 0<k) (P : DFSPartition G A k T) :
    vertexMass (dfsBoxes P) ≤ (1+(T:ℝ)/k)*A.card := by
  simpa only [vertexMass,dfsBoxes,List.map_ofFn,dfsAssigned,Function.comp_def,
    List.sum_ofFn] using dfs_partition_mass_bound hk P

/-- An actual graph partition into DFS boxes, with exact real threshold
payment and explicit floor losses in the overlap factor. -/
theorem exists_dfs_boxes (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) {ell L : ℝ} (hell : 1≤ell) (hL : ell+2<L)
    (hcycle : NoLongCycle G ell) :
    ∃ boxes : List (AssignedPiece V),
      (∀ B∈boxes, B.vertices⊆A ∧ B.vertices.Nonempty ∧ (B.vertices.card:ℝ)≤L) ∧
      (∀ v∈A, ∃ B∈boxes, v∈B.vertices) ∧
      GraphPartition G (boxes.map AssignedPiece.graph) ∧
      vertexMass boxes ≤ (1+2*ell/(L-ell-2))*A.card := by
  let T := ⌊ell⌋₊
  let k := ⌊(L-(T:ℝ))/2⌋₊
  obtain ⟨hk,hT,horder,hratio⟩ := dfs_floor_overlap hell hL
  change 0<k at hk
  change 1≤T at hT
  have hn : NoCycleAtLeast G (T+1) := by
    intro v p hp
    have hh := (hcycle v p hp).trans (Nat.lt_floor_add_one ell)
    exact_mod_cast hh
  obtain ⟨F⟩ := exists_normalDFSForest G
  obtain ⟨P,hPA⟩ := exists_dfsPartition_on_subset_successor F hk hT hn A
    (supported_ancestorClosed hG F)
  refine ⟨dfsBoxes P,?_,?_,dfs_boxes_partition hG P,?_⟩
  · intro B hB
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hB
    refine ⟨hPA i,?_,?_⟩
    · exact (P.block i).core_nonempty.mono (Finset.subset_union_left)
    · have hb : ((P.block i).vertices.card:ℝ)≤(2*k+T:ℕ) := by
        exact_mod_cast dfs_block_order_bound (P.block i)
      exact hb.trans horder
  · intro v hv
    have hh : v∈⋃ i, ((P.block i).core:Set V) := P.core_union.symm ▸ hv
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
    exact ⟨dfsAssigned (P.block i),List.mem_ofFn.mpr ⟨i,rfl⟩,
      Finset.mem_union_left _ hi⟩
  · exact (dfs_boxes_mass hk P).trans (mul_le_mul_of_nonneg_right
      (by linarith only [hratio]) (Nat.cast_nonneg _))

end
end Cycle12
