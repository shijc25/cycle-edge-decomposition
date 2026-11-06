import Cycle12.Foundations.MissingAway

/-! Pull the stopping block's missing edges back through actual host routes.
The counts exclude the vertex itself, agreeing with GLW's f_G convention. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {hj : j+1≤p} (hp : 0<p)
    (A : GLWState G (prefixRho G hp) (j+1) hj)

def neighborEmbedding : A.neighbors ↪ X ⊕ Fin (j+1) :=
  ⟨fun v => v.val.val,fun _ _ h => Subtype.ext (Subtype.ext h)⟩

theorem base_outside_neighbors_le :
    ((baseNeighbors G hp).image (Sum.inl : X → X ⊕ Fin (j+1)) \ univ.image (A.neighborEmbedding hp)).card≤
      baseMissing G hp ⟨j,hj⟩ := by
  let M := (baseNeighbors G hp).filter (fun x => ¬G.Adj (Sum.inr (⟨j,hj⟩ : Fin p)) (Sum.inl x))
  have hsub : (baseNeighbors G hp).image (Sum.inl : X → X ⊕ Fin (j+1)) \ univ.image (A.neighborEmbedding hp) ⊆
      M.image Sum.inl := by
    intro v hv
    obtain ⟨himage,hout⟩ := mem_sdiff.mp hv
    obtain ⟨x,hxB,rfl⟩ := mem_image.mp himage
    refine mem_image.mpr ⟨x,mem_filter.mpr ⟨hxB,?_⟩,rfl⟩
    intro hg
    apply hout
    have hR : A.routes.graph.Adj (lastVertex j) (Sum.inl x) := A.originals hg
    have hxN : keep j (Sum.inl x)∈A.neighbors :=
      ⟨(keep_mem_survivingExternal _).mpr ⟨x,rfl⟩,(A.routes.graph_adj_iff_multiplicity _ _).mp hR |>.2⟩
    exact mem_image.mpr ⟨⟨keep j (Sum.inl x),hxN⟩,mem_univ _,rfl⟩
  have h := card_le_card hsub
  rw [card_image_of_injective _ Sum.inl_injective] at h
  exact h

theorem original_missing_from_neighbor (u : A.neighbors) :
    missingNeighbors (G.comap (Sum.inl : X → X ⊕ Fin p))
      ((baseNeighbors G hp).erase (A.neighborExternal u)) (A.neighborExternal u)≤
      (A.routes.externalGraph (lastVertex j) A.neighbors)ᶜ.degree u+
        baseMissing G hp ⟨j,hj⟩+(p-(j+1)) := by
  let f : X ↪ X ⊕ Fin (j+1) := Function.Embedding.inl
  let B := (baseNeighbors G hp).image f
  let v := (A.neighborEmbedding hp) u
  have hlocal := missing_erase_of_comap A.routes.graph (A.neighborEmbedding hp) B u
  have houtside := A.base_outside_neighbors_le hp
  have hback := A.routes.graphRouting.missing_pullback_le (B.erase v) v
  have hv : v=f (A.neighborExternal u) := (A.neighborExternal_spec u).symm
  have he : missingNeighbors (G.comap A.routes.graphRouting.vertex) (B.erase v) v=
      missingNeighbors (G.comap (Sum.inl : X → X ⊕ Fin p))
        ((baseNeighbors G hp).erase (A.neighborExternal u)) (A.neighborExternal u) := by
    rw [hv]
    change missingNeighbors (G.comap A.routes.graphRouting.vertex)
      (((baseNeighbors G hp).image f).erase (f (A.neighborExternal u))) (f (A.neighborExternal u))=_
    rw [← image_erase f.injective,missing_image]
    rfl
  rw [he] at hback
  simp only [Fintype.card_sum,Fintype.card_fin] at hback
  have hcard : (Fintype.card X+p)-(Fintype.card X+(j+1))=p-(j+1) := by omega
  rw [hcard] at hback
  change missingNeighbors A.routes.graph (B.erase v) v≤
    (A.routes.externalGraph (lastVertex j) A.neighbors)ᶜ.degree u+
      (B \ univ.image (A.neighborEmbedding hp)).card at hlocal
  change (B \ univ.image (A.neighborEmbedding hp)).card≤baseMissing G hp ⟨j,hj⟩ at houtside
  omega

theorem original_missing_block_bound (B : Set A.neighbors)
    (hmiss : ∀ u∈B, (A.routes.externalGraph (lastVertex j) A.neighbors)ᶜ.degree u≤
      B.ncard+(A.routes.doubleExternal (lastVertex j) A.neighbors).card)
    (hordered : ∀ i : Fin p, i.val≠0 →
      baseMissing G hp i≤p+(i.val+1)+prefixRho G hp (i.val+1))
    (u : A.neighbors) (hu : u∈B) :
    missingNeighbors (G.comap (Sum.inl : X → X ⊕ Fin p))
      ((baseNeighbors G hp).erase (A.neighborExternal u)) (A.neighborExternal u)≤
      B.ncard+2*p+prefixRho G hp p := by
  have hback := A.original_missing_from_neighbor hp u
  have hB := hmiss u hu
  have hD := A.doubleExternal_card_le
  have hr := prefixRho_monotone G hp hj
  by_cases hj0 : j=0
  · have hm : baseMissing G hp ⟨j,hj⟩=0 := by subst j; exact baseMissing_root G hp
    rw [hm] at hback
    simp only [hj0,if_true] at hD
    omega
  · have hm := hordered ⟨j,hj⟩ hj0
    change baseMissing G hp ⟨j,hj⟩≤p+(j+1)+prefixRho G hp (j+1) at hm
    simp only [hj0,if_false] at hD
    omega

end GLWState
end
end Cycle13
