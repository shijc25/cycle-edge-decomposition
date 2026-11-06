import Cycle12.Foundations.PackingAssembly

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace CyclePacking
variable {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V}

def mapEmbedding (P : CyclePacking G) (f : V ↪ W) : CyclePacking (G.map f) where
  count := P.count
  parts i := Sym2.map f '' P.parts i
  cycles i := by
    obtain ⟨v,p,hp,he⟩ := P.cycles i
    refine ⟨f v,p.map (SimpleGraph.Embedding.map f G).toHom,hp.map f.injective,?_⟩
    simpa [he,SimpleGraph.Embedding.map] using (p.edgeSet_map (SimpleGraph.Embedding.map f G).toHom).symm
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨a,ha,he⟩ ⟨b,hb,he'⟩
    have hab := Sym2.map.injective f.injective (he.trans he'.symm)
    subst b
    exact Set.disjoint_left.mp (P.disjoint hij) ha hb

theorem used_mapEmbedding (P : CyclePacking G) (f : V ↪ W) :
    (P.mapEmbedding f).used=Sym2.map f '' P.used := by
  simp only [mapEmbedding,used,Set.image_iUnion]

theorem residue_mapEmbedding (P : CyclePacking G) (f : V ↪ W) :
    (P.mapEmbedding f).residue.edgeSet=Sym2.map f '' P.residue.edgeSet := by
  rw [residue,edgeSet_deleteEdges,used_mapEmbedding,SimpleGraph.edgeSet_map,
    residue,edgeSet_deleteEdges,Set.image_sdiff (Sym2.map.injective f.injective)]
  rfl

theorem singles_mapEmbedding (P : CyclePacking G) (f : V ↪ W) :
    (P.mapEmbedding f).singles=P.singles := by
  unfold singles
  rw [residue_mapEmbedding,Set.ncard_image_of_injective _ (Sym2.map.injective f.injective)]

variable {H K : SimpleGraph V}

/-- Combine packings of two edge-disjoint subgraphs; all outside edges remain
as singletons, with an exact count recorded below. -/
def combine (P : CyclePacking H) (Q : CyclePacking K)
    (hH : H ≤ G) (hK : K ≤ G) (hd : Disjoint H.edgeSet K.edgeSet) : CyclePacking G :=
  ofIndexed (I:=Fin P.count ⊕ Fin Q.count) (Sum.elim P.parts Q.parts)
    (by
      intro i
      cases i with
      | inl i =>
        obtain ⟨v,p,hp,he⟩ := P.cycles i
        exact ⟨v,p.mapLe hH,hp.mapLe hH,by simpa only [Sum.elim_inl,Walk.edgeSet_mapLe_eq_edgeSet] using he⟩
      | inr i =>
        obtain ⟨v,p,hp,he⟩ := Q.cycles i
        exact ⟨v,p.mapLe hK,hp.mapLe hK,by simpa only [Sum.elim_inr,Walk.edgeSet_mapLe_eq_edgeSet] using he⟩)
    (by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact P.disjoint (fun he => hij (congrArg Sum.inl he))
        | inr j => exact hd.mono (P.parts_subset i) (Q.parts_subset j)
      | inr i =>
        cases j with
        | inl j => exact hd.symm.mono (Q.parts_subset i) (P.parts_subset j)
        | inr j => exact Q.disjoint (fun he => hij (congrArg Sum.inr he)))

theorem combine_count (P : CyclePacking H) (Q : CyclePacking K)
    (hH : H ≤ G) (hK : K ≤ G) (hd : Disjoint H.edgeSet K.edgeSet) :
    (P.combine Q hH hK hd).count=P.count+Q.count := by
  simp only [combine,ofIndexed,Fintype.card_sum,Fintype.card_fin]

theorem combine_used (P : CyclePacking H) (Q : CyclePacking K)
    (hH : H ≤ G) (hK : K ≤ G) (hd : Disjoint H.edgeSet K.edgeSet) :
    (P.combine Q hH hK hd).used=P.used∪Q.used := by
  unfold combine
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

theorem combine_residue (P : CyclePacking H) (Q : CyclePacking K)
    (hH : H ≤ G) (hK : K ≤ G) (hd : Disjoint H.edgeSet K.edgeSet) :
    (P.combine Q hH hK hd).residue.edgeSet=
      (P.residue.edgeSet∪Q.residue.edgeSet)∪(G.edgeSet\(H.edgeSet∪K.edgeSet)) := by
  simp only [residue,edgeSet_deleteEdges,combine_used]
  ext e
  constructor
  · rintro ⟨he,hnot⟩
    by_cases heH : e∈H.edgeSet
    · exact Or.inl (Or.inl ⟨heH,fun hp => hnot (Or.inl hp)⟩)
    by_cases heK : e∈K.edgeSet
    · exact Or.inl (Or.inr ⟨heK,fun hp => hnot (Or.inr hp)⟩)
    · exact Or.inr ⟨he,fun h => h.elim heH heK⟩
  · rintro ((⟨he,hnot⟩ | ⟨he,hnot⟩) | ⟨he,hnot⟩)
    · refine ⟨edgeSet_mono hH he,?_⟩
      rintro (hp | hq)
      · exact hnot hp
      · exact Set.disjoint_left.mp hd he (Q.used_subset hq)
    · refine ⟨edgeSet_mono hK he,?_⟩
      rintro (hp | hq)
      · exact Set.disjoint_left.mp hd (P.used_subset hp) he
      · exact hnot hq
    · refine ⟨he,?_⟩
      rintro (hp | hq)
      · exact hnot (Or.inl (P.used_subset hp))
      · exact hnot (Or.inr (Q.used_subset hq))

theorem combine_singles (P : CyclePacking H) (Q : CyclePacking K)
    (hH : H ≤ G) (hK : K ≤ G) (hd : Disjoint H.edgeSet K.edgeSet) :
    (P.combine Q hH hK hd).singles=P.singles+Q.singles+
      (G.edgeSet\(H.edgeSet∪K.edgeSet)).ncard := by
  have hPQ := hd.mono (edgeSet_mono P.residue_le) (edgeSet_mono Q.residue_le)
  have hrest : Disjoint (P.residue.edgeSet∪Q.residue.edgeSet)
      (G.edgeSet\(H.edgeSet∪K.edgeSet)) := by
    apply Set.disjoint_left.mpr
    rintro e (hp | hq) ⟨_,he⟩
    · exact he (Or.inl (edgeSet_mono P.residue_le hp))
    · exact he (Or.inr (edgeSet_mono Q.residue_le hq))
  unfold singles
  rw [combine_residue,Set.ncard_union_eq hrest,Set.ncard_union_eq hPQ]

end CyclePacking
end
end Cycle13
