import Cycle12.Foundations.WeightedPacking

namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

theorem ncard_iUnion_disjoint {I X : Type} [Fintype I] [Fintype X]
    (s : I → Set X) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    (⋃ i, s i).ncard = ∑ i, (s i).ncard := by
  classical
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_iUnion]
  rw [Finset.card_biUnion (fun i _ j _ hij => Set.disjoint_toFinset.mpr (hd hij))]

namespace CyclePacking
variable {V W I : Type} [Fintype V] [Fintype W] [Fintype I]
variable {G : SimpleGraph V} {H : SimpleGraph W}

def ofIndexed (parts : I → Set (Sym2 V))
    (hc : ∀ i, ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ parts i = p.edgeSet)
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j))) : CyclePacking G where
  count := Fintype.card I
  parts := fun j => parts ((Fintype.equivFin I).symm j)
  cycles := fun j => hc _
  disjoint := fun _ _ h => hd (fun he => h ((Fintype.equivFin I).symm.injective he))

theorem used_ofIndexed (parts : I → Set (Sym2 V))
    (hc : ∀ i, ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ parts i = p.edgeSet)
    (hd : Pairwise (fun i j => Disjoint (parts i) (parts j))) :
    (ofIndexed parts hc hd).used = ⋃ i, parts i := by
  ext e
  simp only [used, ofIndexed, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨Fintype.equivFin I i, by simpa using hi⟩

def mapIso (P : CyclePacking G) (f : G ≃g H) : CyclePacking H where
  count := P.count
  parts := fun i => Sym2.map f '' P.parts i
  cycles := by
    intro i
    obtain ⟨v, p, hp, he⟩ := P.cycles i
    exact ⟨f v, p.map f.toHom, hp.map f.injective, by simpa [he] using
      (p.edgeSet_map f.toHom).symm⟩
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨a, ha, he⟩ ⟨b, hb, he'⟩
    have hab := Sym2.map.injective f.injective (he.trans he'.symm)
    subst b
    exact Set.disjoint_left.mp (P.disjoint hij) ha hb

theorem used_mapIso (P : CyclePacking G) (f : G ≃g H) :
    (P.mapIso f).used = Sym2.map f '' P.used := by
  simp only [used, mapIso, Set.image_iUnion]

theorem residue_mapIso (P : CyclePacking G) (f : G ≃g H) :
    (P.mapIso f).residue.edgeSet = Sym2.map f '' P.residue.edgeSet := by
  rw [residue, edgeSet_deleteEdges, used_mapIso, residue, edgeSet_deleteEdges,
    Set.image_sdiff (Sym2.map.injective f.injective)]
  have he : Sym2.map f '' G.edgeSet = H.edgeSet := by
    ext e
    constructor
    · rintro ⟨d, hd, rfl⟩
      induction d using Sym2.ind with
      | _ x y => exact f.toHom.map_adj hd
    · intro he
      refine ⟨Sym2.map f.symm e, ?_, ?_⟩
      · induction e using Sym2.ind with
        | _ x y => exact f.symm.toHom.map_adj he
      · induction e using Sym2.ind with
        | _ x y => simp
  rw [he]

theorem cost_mapIso (P : CyclePacking G) (f : G ≃g H) : (P.mapIso f).cost = P.cost := by
  unfold cost singles
  rw [residue_mapIso, Set.ncard_image_of_injective _ (Sym2.map.injective f.injective)]
  rfl

end CyclePacking
end
end Cycle13
