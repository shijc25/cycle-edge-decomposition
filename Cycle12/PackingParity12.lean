import Cycle12.Foundations.ParityForestReduction
import Cycle12.FirstPassReservoirPacking12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open scoped symmDiff
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Deleting any finite packing of simple cycles preserves every degree
parity. This includes arbitrary isolated vertices and the empty packing. -/
theorem packing_residue_parity {G : SimpleGraph V} (P : CyclePacking G) (v : V) :
    Even (P.residue.degree v) ↔ Even (G.degree v) := by
  let H := fromEdgeSet P.used
  have hH : H.edgeSet = P.used := by
    ext e
    rw [show H.edgeSet = P.used \ Sym2.diagSet from edgeSet_fromEdgeSet P.used]
    constructor
    · exact fun he => he.1
    · intro he
      exact ⟨he,not_isDiag_of_mem_edgeSet G (P.used_subset he)⟩
  have hHG : H ≤ G := by
    rw [←edgeSet_subset_edgeSet,hH]
    exact P.used_subset
  have hp : ∀ i, ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ P.parts i = p.edgeSet := P.cycles
  choose start walk hcycle he using hp
  let q : ∀ i, H.Walk (start i) (start i) := fun i => (walk i).transfer H (by
    intro e he'
    rw [hH]
    exact Set.mem_iUnion.mpr ⟨i,(he i).symm ▸ he'⟩)
  have hq : ∀ i, (q i).IsTrail := fun i => (hcycle i).isTrail.transfer _
  have hqe : ∀ i, (q i).edgeSet = P.parts i := by
    intro i
    exact (Walk.edgeSet_transfer _ _).trans (he i).symm
  have hc : (⋃ i, (q i).edgeSet) = H.edgeSet := by simp only [hqe,hH]; rfl
  have hEven : Even (H.degree v) := by
    have hh := trail_partition_even_degree_iff H q hq (by simpa only [hqe] using P.disjoint) hc v
    have hz : Even (univ.filter (fun i : Fin P.count => start i ≠ start i ∧
        (v = start i ∨ v = start i))).card := by simp
    have he := hh.mpr hz
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using he
  have hr : P.residue = G ∆ H := by
    rw [symmDiff_of_ge hHG]
    apply SimpleGraph.edgeSet_injective
    rw [CyclePacking.residue,edgeSet_deleteEdges,edgeSet_sdiff,hH]
  have hh := graph_symmDiff_degree_even G H v
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hEven hh ⊢
  rw [hr]
  tauto

end
end Cycle12
