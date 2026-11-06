import Cycle12.SixResidueModels

namespace Cycle12
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

theorem six_residue_core_mem (counts : Fin 4 → Fin 3) (ear : Fin 5) (i : Fin 6) :
    sixResidueCore i∈sixResidueActive counts ear := by
  exact mem_union.mpr (Or.inl (mem_union.mpr
    (Or.inl (mem_image.mpr ⟨i,mem_univ _,rfl⟩))))

theorem six_residue_slot_mem (counts : Fin 4 → Fin 3) (ear : Fin 5)
    (j : Fin 4) (k : Fin 2) (hk : k.val<(counts j).val) :
    sixResidueSlotVertex j k∈sixResidueActive counts ear := by
  exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_biUnion.mpr
    ⟨j,mem_univ _,mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,hk⟩,rfl⟩⟩))))

theorem six_residue_ring_facts : ∀ e∈sixResidueRing,
    ¬e.IsDiag ∧ e∈((univ:Finset (Fin 6)).image sixResidueCore).sym2 := by decide +kernel

theorem six_residue_chord_facts : ∀ i : Fin 9,
    ¬(sixResidueChord i).IsDiag ∧
      sixResidueChord i∈((univ:Finset (Fin 6)).image sixResidueCore).sym2 := by decide +kernel

theorem six_residue_ear_facts : ∀ ear : Fin 5, ∀ e∈sixResidueEar ear,
    ¬e.IsDiag ∧ e∈(((univ:Finset (Fin 6)).image sixResidueCore) ∪
      (if ear=0 then ∅ else {14,15})).sym2 := by decide +kernel

theorem six_residue_core_sym2_subset (counts : Fin 4 → Fin 3) (ear : Fin 5) :
    ((univ:Finset (Fin 6)).image sixResidueCore).sym2 ⊆
      (sixResidueActive counts ear).sym2 := by
  intro e he
  apply mem_sym2_iff.mpr
  intro x hx
  obtain ⟨i,_,rfl⟩ := mem_image.mp (mem_sym2_iff.mp he x hx)
  exact six_residue_core_mem counts ear i

theorem six_residue_base_facts (t : Fin 14) (counts : Fin 4 → Fin 3) (ear : Fin 5) :
    ∀ e∈sixResidueBase t counts ear,
      ¬e.IsDiag ∧ e∈(sixResidueActive counts ear).sym2 := by
  intro e he
  rcases mem_union.mp he with h | h
  · rcases mem_union.mp h with h | h
    · exact ⟨(six_residue_ring_facts e h).1,
        six_residue_core_sym2_subset counts ear (six_residue_ring_facts e h).2⟩
    · obtain ⟨j,_,hj⟩ := mem_biUnion.mp h
      obtain ⟨k,_,hk⟩ := mem_biUnion.mp hj
      by_cases hcount : k.val<(counts j).val
      · rw [if_pos hcount] at hk
        cases hs : sixResidueSlot t j with
        | none => simp [hs] at hk
        | some i =>
          rw [hs] at hk
          obtain ⟨v,_,rfl⟩ := mem_image.mp hk
          refine ⟨?_,mk_mem_sym2_iff.mpr
            ⟨six_residue_slot_mem counts ear j k hcount,six_residue_core_mem counts ear v⟩⟩
          change sixResidueSlotVertex j k≠sixResidueCore v
          intro he
          have hh := congrArg Fin.val he
          simp only [sixResidueSlotVertex,sixResidueCore] at hh
          omega
      · simp [hcount] at hk
  · refine ⟨(six_residue_ear_facts ear e h).1,?_⟩
    apply mem_sym2_iff.mpr
    intro x hx
    have hm := mem_sym2_iff.mp (six_residue_ear_facts ear e h).2 x hx
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hm
      exact six_residue_core_mem counts ear i
    · exact mem_union.mpr (Or.inr hm)

theorem six_residue_edges_facts (t : Fin 14) (counts : Fin 4 → Fin 3)
    (ear : Fin 5) (S : Finset (Fin 9)) :
    ∀ e∈chordEdges (sixResidueBase t counts ear) sixResidueChord S,
      ¬e.IsDiag ∧ e∈(sixResidueActive counts ear).sym2 := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact six_residue_base_facts t counts ear e he
  · obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact ⟨(six_residue_chord_facts i).1,
      six_residue_core_sym2_subset counts ear (six_residue_chord_facts i).2⟩

theorem six_residue_edges_supported (t : Fin 14) (counts : Fin 4 → Fin 3)
    (ear : Fin 5) (S : Finset (Fin 9)) :
    ∀ x y, (graph (chordEdges (sixResidueBase t counts ear) sixResidueChord S)).Adj x y →
      x∈sixResidueActive counts ear ∧ y∈sixResidueActive counts ear := by
  intro x y hxy
  exact mk_mem_sym2_iff.mp (six_residue_edges_facts t counts ear S _ hxy.1).2

end Cycle12
