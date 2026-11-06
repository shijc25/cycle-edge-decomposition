import Cycle12.Foundations.GLWSizeBounds

/-! Missing-neighbor bounds excluding the vertex itself, as in GLW's f_G.
The final carrier reservoir omits its branch vertices, so this is the exact
interface needed when pulling an obstruction block back to the original graph. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem missing_erase_of_comap {U V : Type} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (G : SimpleGraph V) (f : U ↪ V)
    (B : Finset V) (u : U) :
    missingNeighbors G (B.erase (f u)) (f u)≤
      (G.comap f)ᶜ.degree u+(B \ univ.image f).card := by
  let T := ((G.comap f)ᶜ.neighborFinset u).image f
  have ht : T.card=(G.comap f)ᶜ.degree u := by
    dsimp [T]
    rw [card_image_of_injective _ f.injective,SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (B.erase (f u)).filter (fun v => ¬G.Adj (f u) v)⊆T∪(B \ univ.image f) := by
    intro v hv
    have hB := mem_erase.mp (mem_filter.mp hv).1
    have hnot := (mem_filter.mp hv).2
    by_cases hmem : v∈univ.image f
    · obtain ⟨a,_,rfl⟩ := mem_image.mp hmem
      apply mem_union_left
      apply mem_image.mpr
      refine ⟨a,?_,rfl⟩
      apply ((G.comap f)ᶜ.mem_neighborFinset u a).mpr
      exact ⟨fun h => hB.1 (congrArg f h.symm),hnot⟩
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hB.2,hmem⟩)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  rw [ht] at hh
  exact hh

theorem missing_image {U V : Type} [DecidableEq U] [DecidableEq V]
    (G : SimpleGraph V) (f : U ↪ V) (B : Finset U) (u : U) :
    missingNeighbors G (B.image f) (f u)=missingNeighbors (G.comap f) B u := by
  unfold missingNeighbors
  have he : (B.image f).filter (fun v => ¬G.Adj (f u) v)=
      (B.filter (fun v => ¬(G.comap f).Adj u v)).image f := by
    ext v
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨a,ha,rfl⟩,hn⟩
      exact ⟨a,⟨ha,hn⟩,rfl⟩
    · rintro ⟨a,⟨ha,hn⟩,rfl⟩
      exact ⟨⟨a,ha,rfl⟩,hn⟩
  rw [he,card_image_of_injective _ f.injective]
  rfl

end
end Cycle13
