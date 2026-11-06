import OAI.Combinatorics.CycleDecomposition.Templates
import Cycle12.SoftCycleCounting12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem outline_ports_union (c : CycleOutline G) :
    c.vertices=c.cycle.dropLast.support.toFinset.biUnion (fun z => {c.start z,c.finish z}) := by
  ext v
  rw [c.mem_vertices]
  simp only [mem_biUnion,List.mem_toFinset,mem_insert,mem_singleton]
  constructor
  · rintro ⟨d,hd,hv | hv⟩
    · exact ⟨d.fst,c.fst_mem hd,Or.inr (hv.trans (c.ports d hd).1.symm)⟩
    · exact ⟨d.snd,c.snd_mem hd,Or.inl (hv.trans (c.ports d hd).2.symm)⟩
  · rintro ⟨z,hz,hv | hv⟩
    · obtain ⟨d,hd,he⟩ := c.incoming z hz
      refine ⟨d,hd,Or.inr ?_⟩
      rw [hv,←(c.ports d hd).2,he]
    · obtain ⟨d,hd,he⟩ := c.outgoing z hz
      refine ⟨d,hd,Or.inl ?_⟩
      rw [hv,←(c.ports d hd).1,he]

theorem outline_ports_disjoint (c : CycleOutline G)
    {z w : c.W} (hz : z∈c.cycle.dropLast.support) (hw : w∈c.cycle.dropLast.support)
    (hzw : z≠w) : Disjoint ({c.start z,c.finish z}:Finset V) {c.start w,c.finish w} := by
  apply Finset.disjoint_left.mpr
  intro v hvz hvw
  have hZ : c.project v=z := by
    rcases mem_insert.mp hvz with hv | hv
    · exact hv ▸ (c.projects z hz).1
    · exact (mem_singleton.mp hv) ▸ (c.projects z hz).2
  have hW : c.project v=w := by
    rcases mem_insert.mp hvw with hv | hv
    · exact hv ▸ (c.projects w hw).1
    · exact (mem_singleton.mp hv) ▸ (c.projects w hw).2
  exact hzw (hZ.symm.trans hW)

theorem outline_cyclic_order (c : CycleOutline G) :
    c.cycle.dropLast.support.toFinset.card=c.cycle.length := by
  rw [List.toFinset_card_of_nodup c.isCycle.isPath_dropLast.support_nodup,
    Walk.length_support,Walk.length_dropLast]
  have hh := c.isCycle.three_le_length
  omega

/-- Each switched quotient vertex contributes two distinct original ports;
an unswitched vertex contributes one. Ports of different vertices are disjoint. -/
theorem outline_ports_card (c : CycleOutline G) :
    c.vertices.card=c.cycle.length+Fintype.card c.Switch := by
  have hsum : c.vertices.card=∑ z∈c.cycle.dropLast.support.toFinset,
      ({c.start z,c.finish z}:Finset V).card := by
    rw [outline_ports_union]
    exact Finset.card_biUnion (fun z hz w hw hzw => outline_ports_disjoint c
      (List.mem_toFinset.mp hz) (List.mem_toFinset.mp hw) hzw)
  have hcard (z : c.W) : ({c.start z,c.finish z}:Finset V).card=
      1+(if c.start z≠c.finish z then 1 else 0) := by
    by_cases h : c.start z=c.finish z <;> simp [h]
  have hs : Fintype.card c.Switch=
      (c.cycle.dropLast.support.toFinset.filter (fun z => c.start z≠c.finish z)).card := by
    let e : c.Switch ≃ ↥(c.cycle.dropLast.support.toFinset.filter (fun z => c.start z≠c.finish z)) :=
      Equiv.subtypeEquivRight (fun z => by simp only [mem_filter,List.mem_toFinset])
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  rw [hsum]
  simp_rw [hcard]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.sum_boole,outline_cyclic_order,hs,Nat.cast_id]

end
end Cycle12
