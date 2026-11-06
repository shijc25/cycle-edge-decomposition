import Cycle12.Foundations.DFSPeeling
import Cycle12.Foundations.PackingOperations
import Cycle12.Foundations.ReservoirLift

namespace Cycle13
open SimpleGraph Finset ReservoirPorts
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Edges incident to the next core, within the current remaining graph.
Edges between two boundary vertices are deliberately absent. -/
def peelGraph (G : SimpleGraph V) (S U : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S ∧ (x ∈ U ∨ y ∈ U)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2.1,h.2.1,h.2.2.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem peelGraph_disjoint_remainder (G : SimpleGraph V) (S U : Finset V) :
    Disjoint (peelGraph G S U).edgeSet (internalGraph G (S \ U)).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hr
  induction e using Sym2.ind with
  | _ x y =>
    change G.Adj x y ∧ x∈S ∧ y∈S ∧ (x∈U ∨ y∈U) at he
    change G.Adj x y ∧ x∈S\U ∧ y∈S\U at hr
    rcases he.2.2.2 with h | h
    · exact (Finset.mem_sdiff.mp hr.2.1).2 h
    · exact (Finset.mem_sdiff.mp hr.2.2).2 h

theorem peelGraph_edge_partition (G : SimpleGraph V) (S U : Finset V) :
    (peelGraph G S U).edgeSet ∪ (internalGraph G (S \ U)).edgeSet=
      (internalGraph G S).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    change (G.Adj x y ∧ x∈S ∧ y∈S ∧ (x∈U ∨ y∈U)) ∨
      (G.Adj x y ∧ x∈S\U ∧ y∈S\U) ↔ G.Adj x y ∧ x∈S ∧ y∈S
    simp only [Finset.mem_sdiff]
    tauto

structure DFSBlock (G : SimpleGraph V) (k T : ℕ) where
  core : Finset V
  boundary : Finset V
  graph : SimpleGraph V
  core_nonempty : core.Nonempty
  separate : Disjoint core boundary
  graph_le : graph ≤ G
  supported : ∀ ⦃x y⦄, graph.Adj x y → x ∈ core∪boundary ∧ y ∈ core∪boundary
  size : (core.card ≤ k ∧ boundary=∅) ∨
    (k ≤ core.card ∧ core.card < 2*k ∧ boundary.card ≤ T)

namespace DFSBlock
variable {G : SimpleGraph V} {k T : ℕ}

def vertices (B : DFSBlock G k T) : Finset V := B.core ∪ B.boundary

theorem vertices_card (B : DFSBlock G k T) :
    B.vertices.card=B.core.card+B.boundary.card := Finset.card_union_of_disjoint B.separate

theorem boundary_card (B : DFSBlock G k T) : B.boundary.card ≤ T := by
  rcases B.size with h | h
  · simp [h.2]
  · exact h.2.2

theorem order_le (B : DFSBlock G k T) : B.vertices.card ≤ B.core.card+T := by
  rw [B.vertices_card]
  exact Nat.add_le_add_left B.boundary_card _

def localGraph (B : DFSBlock G k T) : SimpleGraph B.vertices := B.graph.induce (B.vertices:Set V)

theorem lift_localGraph (B : DFSBlock G k T) : reservoirLift B.vertices B.localGraph=B.graph := by
  rw [localGraph,reservoirLift_induce]
  ext x y
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h,B.supported h⟩

theorem local_edges (B : DFSBlock G k T) : B.localGraph.edgeSet.ncard=B.graph.edgeSet.ncard := by
  rw [← B.lift_localGraph,reservoirLift,SimpleGraph.edgeSet_map,
    Set.ncard_image_of_injective _ (reservoirEmbedding B.vertices).sym2Map.injective]

end DFSBlock

structure DFSPartition (G : SimpleGraph V) (S : Finset V) (k T : ℕ) where
  count : ℕ
  block : Fin count → DFSBlock G k T
  core_disjoint : Pairwise (fun i j => Disjoint (block i).core (block j).core)
  core_union : (⋃ i, ((block i).core:Set V))=(S:Set V)
  edge_disjoint : Pairwise (fun i j => Disjoint (block i).graph.edgeSet (block j).graph.edgeSet)
  edge_union : (⋃ i, (block i).graph.edgeSet)=(internalGraph G S).edgeSet

namespace DFSPartition
variable {G : SimpleGraph V} {S : Finset V} {k T : ℕ}

theorem core_subset (P : DFSPartition G S k T) (i : Fin P.count) : (P.block i).core ⊆ S := by
  intro v hv
  have hh : v ∈ ⋃ i, ((P.block i).core:Set V) := Set.mem_iUnion.mpr ⟨i,hv⟩
  rwa [P.core_union] at hh

theorem edge_subset (P : DFSPartition G S k T) (i : Fin P.count) :
    (P.block i).graph.edgeSet ⊆ (internalGraph G S).edgeSet := by
  intro e he
  rw [← P.edge_union]
  exact Set.mem_iUnion.mpr ⟨i,he⟩

theorem sum_core_card (P : DFSPartition G S k T) :
    ∑ i, (P.block i).core.card=S.card := by
  have hh := ncard_iUnion_disjoint (fun i => ((P.block i).core:Set V))
    (fun i j hij => Finset.disjoint_coe.mpr (P.core_disjoint hij))
  simpa only [P.core_union,Set.ncard_coe_finset] using hh.symm

theorem sum_edges (P : DFSPartition G S k T) :
    ∑ i, (P.block i).graph.edgeSet.ncard=(internalGraph G S).edgeSet.ncard := by
  rw [← P.edge_union,ncard_iUnion_disjoint _ P.edge_disjoint]

end DFSPartition

/-- The full DFS partition, including exact original-edge ownership.
Core vertices partition S; boundary vertices may be shared. -/
theorem exists_dfsPartition_on {G : SimpleGraph V} (F : NormalDFSForest G)
    {k T : ℕ} (hk : 0 < k) (hT : 1 ≤ T) (hG : NoCycleAtLeast G T)
    (S : Finset V) (hS : F.AncestorClosed S) : Nonempty (DFSPartition G S k T) := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hSne : S.Nonempty
    · obtain ⟨U,hUS,hUn,hclosed,hsize⟩ := F.exists_peel hS hSne hk hT hG
      have hsmall : (S\U).card < n := by
        rw [Finset.card_sdiff_of_subset hUS]
        have hpos := Finset.card_pos.mpr hUn
        have hle := Finset.card_le_card hUS
        omega
      obtain ⟨P⟩ := ih _ hsmall (S\U) hclosed rfl
      let B : DFSBlock G k T := {
        core := U
        boundary := externalWithin G S U
        graph := peelGraph G S U
        core_nonempty := hUn
        separate := by
          apply Finset.disjoint_left.mpr
          intro x hx he
          exact ((mem_externalWithin _ _ _ _).mp he).2.1 hx
        graph_le := fun _ _ h => h.1
        supported := by
          intro x y hxy
          obtain ⟨hxy,hxS,hyS,hU⟩ := hxy
          constructor
          · by_cases hxU : x∈U
            · exact Finset.mem_union_left _ hxU
            · have hyU : y∈U := hU.resolve_left hxU
              exact Finset.mem_union_right _ ((mem_externalWithin _ _ _ _).mpr
                ⟨hxS,hxU,y,hyU,hxy.symm⟩)
          · by_cases hyU : y∈U
            · exact Finset.mem_union_left _ hyU
            · have hxU : x∈U := hU.resolve_right hyU
              exact Finset.mem_union_right _ ((mem_externalWithin _ _ _ _).mpr
                ⟨hyS,hyU,x,hxU,hxy⟩)
        size := hsize }
      have hcore : ∀ i, Disjoint B.core (P.block i).core := by
        intro i
        apply Finset.disjoint_left.mpr
        intro v hv hi
        exact (Finset.mem_sdiff.mp (P.core_subset i hi)).2 hv
      have hedge : ∀ i, Disjoint B.graph.edgeSet (P.block i).graph.edgeSet :=
        fun i => (peelGraph_disjoint_remainder G S U).mono_right (P.edge_subset i)
      refine ⟨{
        count := P.count+1
        block := Fin.cases B P.block
        core_disjoint := ?_
        core_union := ?_
        edge_disjoint := ?_
        edge_union := ?_ }⟩
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact hcore j
        | succ i =>
          induction j using Fin.cases with
          | zero => exact (hcore i).symm
          | succ j => exact P.core_disjoint (fun h => hij (congrArg Fin.succ h))
      · rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
        change (U:Set V) ∪ (⋃ i, ((P.block i).core:Set V))=(S:Set V)
        rw [P.core_union]
        ext v
        simp only [Set.mem_union,Finset.mem_coe,Finset.mem_sdiff]
        constructor
        · rintro (h | h)
          · exact hUS h
          · exact h.1
        · intro h
          by_cases hv : v∈U
          · exact Or.inl hv
          · exact Or.inr ⟨h,hv⟩
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact hedge j
        | succ i =>
          induction j using Fin.cases with
          | zero => exact (hedge i).symm
          | succ j => exact P.edge_disjoint (fun h => hij (congrArg Fin.succ h))
      · rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
        change (peelGraph G S U).edgeSet ∪ (⋃ i, (P.block i).graph.edgeSet)=_
        rw [P.edge_union]
        exact peelGraph_edge_partition G S U
    · have hSe : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      subst S
      refine ⟨⟨0,Fin.elim0,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i,?_⟩⟩
      · simp
      · simp only [Set.iUnion_of_empty]
        have he : internalGraph G ∅=⊥ := by ext x y; simp [internalGraph]
        rw [he,SimpleGraph.edgeSet_bot]

theorem exists_dfsPartition (G : SimpleGraph V) {k T : ℕ}
    (hk : 0 < k) (hT : 1 ≤ T) (hG : NoCycleAtLeast G T) :
    Nonempty (DFSPartition G univ k T) := by
  obtain ⟨F⟩ := exists_normalDFSForest G
  exact exists_dfsPartition_on F hk hT hG univ (by intro x hx y hy; exact Finset.mem_univ y)

end
end Cycle13
