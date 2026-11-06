import Cycle12.SixResidueDomain
import Cycle12.CycleWordEmbedding

namespace Cycle12
open SimpleGraph Finset TerminalCert
set_option maxHeartbeats 4000000

def sixResidueChordEnds : Fin 9 → (Fin 6 × Fin 6) :=
  ![(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)]

theorem six_residue_chord_endpoints : ∀ i,
    sixResidueChord i=s(sixResidueCore (sixResidueChordEnds i).1,
      sixResidueCore (sixResidueChordEnds i).2) := by decide +kernel

theorem six_residue_ring_image : sixResidueRing=
    (univ:Finset (Fin 6)).image (fun i => s(sixResidueCore i,sixResidueCore (i+1))) := by
  decide +kernel

theorem six_residue_core_pair_coverage : ∀ i j : Fin 6, i≠j →
    s(sixResidueCore i,sixResidueCore j)∈sixResidueRing ∨
      ∃ k : Fin 9, sixResidueChord k=s(sixResidueCore i,sixResidueCore j) := by decide +kernel

theorem six_residue_spoke_edge (t : Fin 14) (counts : Fin 4 → Fin 3) (ear : Fin 5)
    (j : Fin 4) (k : Fin (counts j).val) (a : Fin 11) (ha : sixResidueSlot t j=some a)
    (i : Fin 6) (hi : i∈sixAttachment a) :
    s(sixResidueIndex counts ear (.inr (.inl ⟨j,k⟩)),sixResidueCore i)∈sixResidueSpokes t counts := by
  let k' : Fin 2 := ⟨k.val,by have := k.isLt; have := (counts j).isLt; omega⟩
  apply mem_biUnion.mpr
  refine ⟨j,mem_univ _,mem_biUnion.mpr ⟨k',mem_univ _,?_⟩⟩
  rw [if_pos k.isLt,ha]
  exact mem_image.mpr ⟨i,hi,rfl⟩

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Convert an actual bijective labeling with complete exterior
neighborhoods into one of the chord models. All core chords are retained. -/
theorem six_residue_realization (G : SimpleGraph V)
    (t : Fin 14) (counts : Fin 4 → Fin 3) (ear : Fin 5)
    (r : SixResidueDomain counts ear ↪ V)
    (hcycle : ∀ i, G.Adj (r (.inl i)) (r (.inl (i+1))))
    (hspokes : ∀ j (k : Fin (counts j).val), ∃ a : Fin 11,
      sixResidueSlot t j=some a ∧ ∀ v, G.Adj (r (.inr (.inl ⟨j,k⟩))) v ↔
        ∃ i∈sixAttachment a, r (.inl i)=v)
    (g : Fin 16 → V) (hg : ∀ v, g (sixResidueIndex counts ear v)=r v)
    (hear : ∀ x y, s(x,y)∈sixResidueEar ear → G.Adj (g x) (g y))
    (hfullEar : ∀ k : {k : Fin 2 // ear≠0}, ∀ v,
      G.Adj (r (.inr (.inr k))) (r v) →
        s(sixResidueIndex counts ear (.inr (.inr k)),sixResidueIndex counts ear v)∈sixResidueEar ear) :
    ∃ S : Finset (Fin 9), G.comap r=
      (graph (chordEdges (sixResidueBase t counts ear) sixResidueChord S)).comap
        (sixResidueIndex counts ear) := by
  let S : Finset (Fin 9) := univ.filter
    (fun i => sixResidueChord i∈(G.comap g).edgeSet)
  let E := chordEdges (sixResidueBase t counts ear) sixResidueChord S
  have hcore (i : Fin 6) : g (sixResidueCore i)=r (.inl i) := hg (.inl i)
  have hsnd : ∀ x y, s(x,y)∈E → G.Adj (g x) (g y) := by
    intro x y he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · rcases mem_union.mp he with he | he
        · rw [six_residue_ring_image] at he
          obtain ⟨i,_,hi⟩ := mem_image.mp he
          exact adj_of_sym2_eq g (by simpa only [hcore] using hcycle i) hi
        · obtain ⟨j,_,hj⟩ := mem_biUnion.mp he
          obtain ⟨k,_,hk⟩ := mem_biUnion.mp hj
          by_cases hcount : k.val<(counts j).val
          · rw [if_pos hcount] at hk
            cases ha : sixResidueSlot t j with
            | none => simp [ha] at hk
            | some a =>
              rw [ha] at hk
              obtain ⟨i,hi,hie⟩ := mem_image.mp hk
              obtain ⟨a',ha',hn⟩ := hspokes j ⟨k.val,hcount⟩
              have haa : a'=a := Option.some.inj (ha'.symm.trans ha)
              subst a'
              have hadj := (hn (r (.inl i))).mpr ⟨i,hi,rfl⟩
              apply adj_of_sym2_eq g _ hie
              have hh := hg (.inr (.inl ⟨j,⟨k.val,hcount⟩⟩))
              change g (sixResidueSlotVertex j k)=r (.inr (.inl ⟨j,⟨k.val,hcount⟩⟩)) at hh
              rwa [hh,hcore]
          · simp [hcount] at hk
      · exact hear x y he
    · obtain ⟨i,hi,hie⟩ := mem_image.mp he
      have hm := (mem_filter.mp hi).2
      rw [hie] at hm
      exact hm
  have hspokeComplete : ∀ j (k : Fin (counts j).val) v,
      G.Adj (r (.inr (.inl ⟨j,k⟩))) (r v) →
        s(sixResidueIndex counts ear (.inr (.inl ⟨j,k⟩)),sixResidueIndex counts ear v)∈E := by
    intro j k v hv
    obtain ⟨a,ha,hn⟩ := hspokes j k
    obtain ⟨i,hi,he⟩ := (hn (r v)).mp hv
    have he' := r.injective he
    subst v
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr
      (Or.inr (six_residue_spoke_edge t counts ear j k a ha i hi))))))
  refine ⟨S,?_⟩
  ext u v
  change G.Adj (r u) (r v) ↔
    s(sixResidueIndex counts ear u,sixResidueIndex counts ear v)∈E ∧
      sixResidueIndex counts ear u≠sixResidueIndex counts ear v
  constructor
  · intro huv
    refine ⟨?_,fun he => huv.ne (congrArg r (six_residue_index_injective counts ear he))⟩
    rcases u with i | (⟨j,k⟩ | k)
    · rcases v with l | (⟨j,k⟩ | k)
      · have hil : i≠l := fun he => huv.ne (by cases he; rfl)
        rcases six_residue_core_pair_coverage i l hil with hr | ⟨c,hc⟩
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hr)))))
        · apply mem_union.mpr ∘ Or.inr
          refine mem_image.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,?_⟩,hc⟩
          rw [hc]
          change G.Adj (g (sixResidueCore i)) (g (sixResidueCore l))
          rwa [hcore,hcore]
      · simpa only [Sym2.eq_swap] using hspokeComplete j k (.inl i) huv.symm
      · have hh := hfullEar k (.inl i) huv.symm
        exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (by simpa only [Sym2.eq_swap] using hh))))
    · exact hspokeComplete j k v huv
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (hfullEar k v huv))))
  · intro huv
    simpa only [hg] using hsnd _ _ huv.1

end
end Cycle12
