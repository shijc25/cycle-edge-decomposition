import Cycle12.Foundations.SeedAppend

/-! Append a nonempty external block to an ordered seed. Its original-graph
missing bound implies every required inequality for the enlarged seed. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def finsetEmbedding {V : Type} (B : Finset V) : Fin B.card ↪ V :=
  (Finset.equivFin B).symm.toEmbedding.trans (Function.Embedding.subtype _)

theorem finsetEmbedding_mem {V : Type} (B : Finset V) (i : Fin B.card) : finsetEmbedding B i∈B :=
  ((Finset.equivFin B).symm i).property

theorem finsetEmbedding_image {V : Type} [DecidableEq V] (B : Finset V) :
    univ.image (finsetEmbedding B)=B := by
  ext v
  constructor
  · rintro hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact finsetEmbedding_mem B i
  · intro hv
    obtain ⟨i,hi⟩ := (Finset.equivFin B).symm.surjective ⟨v,hv⟩
    exact mem_image.mpr ⟨i,mem_univ _,congrArg Subtype.val hi⟩

theorem missingNeighbors_mono {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {B C : Finset V} (hBC : B⊆C) (v : V) : missingNeighbors G B v ≤ missingNeighbors G C v := by
  apply card_le_card
  exact filter_subset_filter _ hBC

namespace OrderedSeed
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V} {t p : ℕ}
    (A : OrderedSeed G root t p) (B : Finset V)

def blockVertexDisjoint (hout : ∀ x∈B, x∉univ.image A.vertex) :
    ∀ i j, A.vertex i≠finsetEmbedding B j := by
  intro i j he
  exact hout _ (finsetEmbedding_mem B j) (mem_image.mpr ⟨i,mem_univ _,he⟩)

def extend (hout : ∀ x∈B, x∉univ.image A.vertex) (hsmall : p+B.card<t)
    (hmiss : ∀ x∈B, missingNeighbors G ((seedReservoir G root A.vertex).erase x) x≤
      B.card+2*p+seedRho G root A.vertex p) : OrderedSeed G root t (p+B.card) where
  positive := by have h := A.positive; omega
  small := hsmall
  vertex := appendVertices A.vertex (finsetEmbedding B) (A.blockVertexDisjoint B hout)
  first := by
    change appendVertices A.vertex (finsetEmbedding B) (A.blockVertexDisjoint B hout)
      ((⟨0,A.positive⟩ : Fin p).castAdd B.card)=root
    rw [appendVertices_left,A.first]
  missing := by
    intro i
    obtain ⟨s,rfl⟩ := finSumFinEquiv.surjective i
    let b := finsetEmbedding B
    let hd := A.blockVertexDisjoint B hout
    have hres : seedReservoir G root (appendVertices A.vertex b hd)=seedReservoir G root A.vertex \ B := by
      rw [seedReservoir_append,finsetEmbedding_image]
    cases s with
    | inl k =>
      change missingNeighbors G (seedReservoir G root (appendVertices A.vertex b hd))
        (appendVertices A.vertex b hd (k.castAdd B.card))≤_
      rw [appendVertices_left,hres]
      have hm := missingNeighbors_mono G (sdiff_subset (s:=seedReservoir G root A.vertex) (t:=B)) (A.vertex k)
      have ho := A.missing k
      have hr := seedRho_append_prefix G root A.vertex b hd (show k.val+1≤p from k.isLt)
      change _≤p+B.card+k.val+1+seedRho G root (appendVertices A.vertex b hd) (k.val+1)
      rw [hr]
      omega
    | inr k =>
      change missingNeighbors G (seedReservoir G root (appendVertices A.vertex b hd))
        (appendVertices A.vertex b hd (k.natAdd p))≤_
      rw [appendVertices_right,hres]
      have hsub : seedReservoir G root A.vertex \ B⊆(seedReservoir G root A.vertex).erase (b k) := by
        intro v hv
        have hh := mem_sdiff.mp hv
        exact mem_erase.mpr ⟨fun he => hh.2 (he ▸ finsetEmbedding_mem B k),hh.1⟩
      have hm := missingNeighbors_mono G hsub (b k)
      have ho := hmiss (b k) (finsetEmbedding_mem B k)
      have hr := seedRho_append_lower G root A.vertex b hd (show p≤p+k.val+1 by omega)
      change _≤p+B.card+(p+k.val)+1+seedRho G root (appendVertices A.vertex b hd) (p+k.val+1)
      omega

theorem block_large_of_maximal
    (hmax : ∀ q, Nonempty (OrderedSeed G root t q) → q≤p)
    (hB : B.Nonempty) (hout : ∀ x∈B, x∉univ.image A.vertex)
    (hmiss : ∀ x∈B, missingNeighbors G ((seedReservoir G root A.vertex).erase x) x≤
      B.card+2*p+seedRho G root A.vertex p) : t-p≤B.card := by
  by_contra h
  have hsmall : p+B.card<t := by have hp := A.small; omega
  have he := hmax (p+B.card) ⟨A.extend B hout hsmall hmiss⟩
  have hpos := card_pos.mpr hB
  omega

end OrderedSeed
end
end Cycle13
