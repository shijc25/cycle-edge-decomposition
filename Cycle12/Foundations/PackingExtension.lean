import Cycle12.Foundations.PackingEmbedding

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}

namespace CyclePacking

/-- Continue on precisely the unused original edges. -/
def extend (P : CyclePacking G) (Q : CyclePacking P.residue) : CyclePacking G :=
  ofIndexed (I:=Fin P.count ⊕ Fin Q.count) (Sum.elim P.parts Q.parts)
    (by
      intro i
      cases i with
      | inl i => exact P.cycles i
      | inr i =>
        obtain ⟨v,p,hp,he⟩ := Q.cycles i
        exact ⟨v,p.mapLe P.residue_le,hp.mapLe _,by simpa only
          [Sum.elim_inr,Walk.edgeSet_mapLe_eq_edgeSet] using he⟩)
    (by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact P.disjoint (fun h => hij (congrArg Sum.inl h))
        | inr j => exact (P.residue_disjoint_part i).symm.mono_right (Q.parts_subset j)
      | inr i =>
        cases j with
        | inl j => exact (P.residue_disjoint_part j).mono_left (Q.parts_subset i)
        | inr j => exact Q.disjoint (fun h => hij (congrArg Sum.inr h)))

theorem extend_count (P : CyclePacking G) (Q : CyclePacking P.residue) :
    (P.extend Q).count=P.count+Q.count := by
  simp only [extend,ofIndexed,Fintype.card_sum,Fintype.card_fin]

theorem extend_used (P : CyclePacking G) (Q : CyclePacking P.residue) :
    (P.extend Q).used=P.used ∪ Q.used := by
  unfold extend
  erw [used_ofIndexed]
  unfold used
  ext e
  simp only [Set.mem_iUnion,Set.mem_union]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | inl i => exact Or.inl ⟨i,hi⟩
    | inr i => exact Or.inr ⟨i,hi⟩
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · exact ⟨Sum.inl i,hi⟩
    · exact ⟨Sum.inr i,hi⟩

theorem extend_residue (P : CyclePacking G) (Q : CyclePacking P.residue) :
    (P.extend Q).residue=Q.residue := by
  apply SimpleGraph.edgeSet_injective
  simp only [residue,edgeSet_deleteEdges,extend_used]
  ext e
  simp only [Set.mem_sdiff,Set.mem_union]
  tauto

theorem extend_singles (P : CyclePacking G) (Q : CyclePacking P.residue) :
    (P.extend Q).singles=Q.singles := by rw [singles,extend_residue]; rfl

def weight (P : CyclePacking G) : ℝ := (P.count:ℝ)+(23/42:ℝ)*P.singles

theorem weight_nonneg (P : CyclePacking G) : 0 ≤ P.weight := by unfold weight; positivity

theorem cost_eq_weight (P : CyclePacking G) : (P.cost:ℝ)=42*P.weight := by
  simp only [cost,weight,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem extend_weight (P : CyclePacking G) (Q : CyclePacking P.residue) :
    (P.extend Q).weight=(P.count:ℝ)+Q.weight := by
  simp only [weight,extend_count,extend_singles,Nat.cast_add]
  ring

theorem weight_empty (G : SimpleGraph V) :
    (empty G).weight=(23/42:ℝ)*G.edgeSet.ncard := by
  simp [weight,empty,singles,residue,used]

end CyclePacking
end
end Cycle13
