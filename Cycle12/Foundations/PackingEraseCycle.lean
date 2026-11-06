import Cycle12.Foundations.PackingEmbedding

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cycle_length_le_order {G : SimpleGraph V} {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.length ≤ Fintype.card V := by
  have hh := hp.support_nodup.length_le_card (α:=V)
  simpa only [List.length_tail,Walk.length_support,Nat.add_sub_cancel] using hh

theorem cycle_edgeSet_ncard {G : SimpleGraph V} {v : V} {p : G.Walk v v} (hp : p.IsCycle) :
    p.edgeSet.ncard=p.length := by
  rw [← p.coe_edges_toFinset,Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.isTrail.edges_nodup]
  exact p.length_edges

namespace CyclePacking
variable {G : SimpleGraph V}

def eraseCycle (P : CyclePacking G) (i : Fin P.count) : CyclePacking G :=
  ofIndexed (I:={j : Fin P.count // j ≠ i}) (fun j => P.parts j.val)
    (fun j => P.cycles j.val)
    (fun j k hne => P.disjoint (fun he => hne (Subtype.ext he)))

theorem count_eraseCycle (P : CyclePacking G) (i : Fin P.count) :
    (P.eraseCycle i).count+1=P.count := by
  change Fintype.card {j : Fin P.count // ¬j=i}+1=P.count
  rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
  have hi := i.isLt
  omega

theorem used_eraseCycle (P : CyclePacking G) (i : Fin P.count) :
    (P.eraseCycle i).used=P.used\P.parts i := by
  unfold eraseCycle
  erw [used_ofIndexed]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨Set.mem_iUnion.mpr ⟨j.val,hj⟩,?_⟩
    exact fun hi => Set.disjoint_left.mp (P.disjoint j.property) hj hi
  · rintro ⟨he,hi⟩
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    exact Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩

theorem residue_eraseCycle (P : CyclePacking G) (i : Fin P.count) :
    (P.eraseCycle i).residue.edgeSet=P.residue.edgeSet∪P.parts i := by
  simp only [residue,edgeSet_deleteEdges,used_eraseCycle]
  ext e
  constructor
  · rintro ⟨he,hnot⟩
    by_cases hi : e∈P.parts i
    · exact Or.inr hi
    · exact Or.inl ⟨he,fun hu => hnot ⟨hu,hi⟩⟩
  · rintro (⟨he,hnot⟩ | he)
    · exact ⟨he,fun hu => hnot hu.1⟩
    · exact ⟨P.parts_subset i he,fun hu => hu.2 he⟩

theorem singles_eraseCycle (P : CyclePacking G) (i : Fin P.count) :
    (P.eraseCycle i).singles=P.singles+(P.parts i).ncard := by
  unfold singles
  rw [residue_eraseCycle,Set.ncard_union_eq (P.residue_disjoint_part i)]

/-- Removing one selected cycle loses at most the ambient order in covered
edges. This pays for rounding a real cycle budget down to an integer. -/
theorem singles_eraseCycle_le (P : CyclePacking G) (i : Fin P.count) :
    (P.eraseCycle i).singles ≤ P.singles+Fintype.card V := by
  rw [singles_eraseCycle]
  apply Nat.add_le_add_left
  obtain ⟨v,p,hp,he⟩ := P.cycles i
  rw [he,cycle_edgeSet_ncard hp]
  exact cycle_length_le_order hp

end CyclePacking
end
end Cycle13
