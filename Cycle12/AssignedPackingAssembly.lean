import Cycle12.PartitionPacking

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem indexed_partition_exists_packing {G : SimpleGraph V} {n : ℕ}
    (F : Fin n → SimpleGraph V) (hp : GraphPartition G (List.ofFn F))
    (Q : ∀ i, CyclePacking (F i)) :
    ∃ P : CyclePacking G, P.weight=∑ i, (Q i).weight := by
  have hle : ∀ i, F i≤G := fun i => partition_member_le hp (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hd : Pairwise (fun i j => Disjoint (F i).edgeSet (F j).edgeSet) := by
    intro i j hij
    have hh := List.pairwise_iff_getElem.mp (graphPartition_pairwise hp)
    rcases lt_or_gt_of_ne (show i.val≠j.val from fun h => hij (Fin.ext h)) with h | h
    · have hr := hh i.val j.val
        (by simpa only [List.length_ofFn] using i.isLt)
        (by simpa only [List.length_ofFn] using j.isLt) h
      simpa only [List.getElem_ofFn] using hr
    · have hr := hh j.val i.val
        (by simpa only [List.length_ofFn] using j.isLt)
        (by simpa only [List.length_ofFn] using i.isLt) h
      simpa only [List.getElem_ofFn] using hr.symm
  have hu : (⋃ i, (F i).edgeSet)=G.edgeSet := by
    rw [←graphPartition_union hp]
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet,graphUnion_adj,List.mem_ofFn]
      constructor
      · rintro ⟨i,hi⟩; exact ⟨F i,⟨i,rfl⟩,hi⟩
      · rintro ⟨H,⟨i,rfl⟩,hi⟩; exact ⟨i,hi⟩
  let P := CyclePacking.assemble F hle hd Q
  refine ⟨P,?_⟩
  have hc := CyclePacking.assemble_cost F hle hd hu Q
  have he : (P.cost:ℝ)=∑ i, ((Q i).cost:ℝ) := by exact_mod_cast hc
  simp_rw [CyclePacking.cost_eq_weight] at he
  rw [←Finset.mul_sum] at he
  linarith only [he]

theorem assigned_partition_packing_bound {G : SimpleGraph V} (L : List (AssignedPiece V))
    (hp : GraphPartition G (L.map AssignedPiece.graph)) {C : ℝ}
    (hcost : ∀ P∈L, ∃ Q : CyclePacking P.graph, Q.weight≤C*P.vertices.card) :
    ∃ Q : CyclePacking G, Q.weight≤C*vertexMass L := by
  have he : List.ofFn (fun i : Fin L.length => (L.get i).graph)=L.map AssignedPiece.graph := by
    change List.ofFn (AssignedPiece.graph ∘ L.get)=L.map AssignedPiece.graph
    rw [←List.map_ofFn,List.ofFn_get]
  have hp' : GraphPartition G (List.ofFn (fun i : Fin L.length => (L.get i).graph)) := he.symm ▸ hp
  choose Q hQ using fun i : Fin L.length => hcost (L.get i) (L.get_mem i)
  obtain ⟨P,hP⟩ := indexed_partition_exists_packing _ hp' Q
  refine ⟨P,?_⟩
  rw [hP]
  calc
    _ ≤ ∑ i : Fin L.length, C*((L.get i).vertices.card:ℝ) := Finset.sum_le_sum (fun i _ => hQ i)
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      exact list_sum_get L (fun P => (P.vertices.card:ℝ))

theorem partition_segment {G : SimpleGraph V} {A B C : List (SimpleGraph V)}
    (hp : GraphPartition G (A++B++C)) : GraphPartition (graphUnion B) B := by
  apply graphPartition_of_le_one
  intro x y
  have hh := hp x y
  simp only [edgeOccurrences_append] at hh
  split_ifs at hh <;> omega

theorem partition_three_groups {G : SimpleGraph V} {A B C : List (SimpleGraph V)}
    (hp : GraphPartition G (A++B++C)) :
    GraphPartition G [graphUnion A,graphUnion B,graphUnion C] := by
  have hA : GraphPartition (graphUnion A) A := partition_segment (A:=[])
    (C:=B++C) (by simpa only [List.nil_append,List.append_assoc] using hp)
  have hB := partition_segment hp
  have hC : GraphPartition (graphUnion C) C := partition_segment (A:=A++B)
    (C:=[]) (by simpa only [List.append_nil] using hp)
  intro x y
  have hh := hp x y
  simp only [edgeOccurrences_append,hA x y,hB x y,hC x y] at hh
  simpa only [edgeOccurrences_cons,edgeOccurrences_nil,Nat.add_zero,Nat.add_assoc] using hh

theorem three_packing_bound {G H0 H1 H2 : SimpleGraph V}
    (hp : GraphPartition G [H0,H1,H2])
    (P0 : CyclePacking H0) (P1 : CyclePacking H1) (P2 : CyclePacking H2) :
    ∃ P : CyclePacking G, P.weight=P0.weight+P1.weight+P2.weight := by
  let F : Fin 3 → SimpleGraph V := ![H0,H1,H2]
  let Q : ∀ i, CyclePacking (F i) := Fin.cases P0 (Fin.cases P1 (Fin.cases P2 (fun i => Fin.elim0 i)))
  have hp' : GraphPartition G (List.ofFn F) := by simpa [F,List.ofFn_succ] using hp
  obtain ⟨P,hP⟩ := indexed_partition_exists_packing F hp' Q
  refine ⟨P,?_⟩
  rw [hP]
  have hq0 : (Q 0).weight=P0.weight := rfl
  have hq1 : (Q 1).weight=P1.weight := rfl
  have hq2 : (Q 2).weight=P2.weight := rfl
  simp only [Fin.sum_univ_three,hq0,hq1,hq2]

end
end Cycle12
