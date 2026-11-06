import Cycle12.LayerRemainder
import Cycle12.Foundations.PackingAssembly
import Cycle12.Foundations.PackingExtension

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem partition_exists_packing {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (hp : GraphPartition G L) (Q : ∀ i : Fin L.length, CyclePacking (L.get i)) :
    ∃ P : CyclePacking G, P.weight=∑ i, (Q i).weight := by
  have hle : ∀ i : Fin L.length, L.get i≤G := fun i => partition_member_le hp (L.get_mem i)
  have hd : Pairwise (fun i j : Fin L.length => Disjoint (L.get i).edgeSet (L.get j).edgeSet) :=
    list_pairwise_get (graphPartition_pairwise hp) (fun _ _ h => h.symm)
  have hu : (⋃ i : Fin L.length, (L.get i).edgeSet)=G.edgeSet := by
    rw [graphUnion_edges,graphPartition_union hp]
  let P := CyclePacking.assemble (fun i : Fin L.length => L.get i) hle hd Q
  refine ⟨P,?_⟩
  have hcost := CyclePacking.assemble_cost (fun i : Fin L.length => L.get i) hle hd hu Q
  have he : (P.cost:ℝ)=∑ i, ((Q i).cost:ℝ) := by exact_mod_cast hcost
  simp_rw [CyclePacking.cost_eq_weight] at he
  rw [← Finset.mul_sum] at he
  linarith only [he]

theorem partition_packing_bound {G : SimpleGraph V} {L : List (SimpleGraph V)}
    (hp : GraphPartition G L) (fee : SimpleGraph V → ℝ)
    (hfee : ∀ H∈L, ∃ Q : CyclePacking H, Q.weight≤fee H) :
    ∃ P : CyclePacking G, P.weight≤(L.map fee).sum := by
  choose Q hQ using fun i : Fin L.length => hfee (L.get i) (L.get_mem i)
  obtain ⟨P,hP⟩ := partition_exists_packing hp Q
  refine ⟨P,?_⟩
  rw [hP,←list_sum_get L fee]
  exact Finset.sum_le_sum (fun i _ => hQ i)

theorem cycle_graph_packing {G : SimpleGraph V} (hG : IsCycleGraph G) :
    ∃ P : CyclePacking G, P.weight=1 := by
  obtain ⟨v,p,hp,he⟩ := hG
  let P : CyclePacking G := {
    count := 1
    parts := fun _ => G.edgeSet
    cycles := fun _ => ⟨v,p,hp,he⟩
    disjoint := fun i j hij => False.elim (hij (Subsingleton.elim _ _)) }
  have hu : P.used=G.edgeSet := by
    simp only [CyclePacking.used,P,Set.iUnion_const]
  have hs : P.singles=0 := by
    simp only [CyclePacking.singles,CyclePacking.residue,SimpleGraph.edgeSet_deleteEdges,hu,
      Set.diff_self,Set.ncard_empty]
  refine ⟨P,?_⟩
  have hc : P.count=1 := rfl
  rw [CyclePacking.weight,hc,hs]
  norm_num

end
end Cycle12
