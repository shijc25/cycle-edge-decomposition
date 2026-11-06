import Cycle12.Foundations.GLWBlockPullback

/-! The controlled suppression argument assembled from actual graph data:
a minimal bad Eulerian graph and an ordered seed give a nonempty external
block, with the original graph's missing-neighbor bound. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

theorem glw_nonempty_external_block {X : Type} [Fintype X] [DecidableEq X]
    {p d t : ℕ} (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) (hpt : p<t)
    (hd : 7*t≤d) (hdegree : d≤G.degree (Sum.inr ⟨0,hp⟩))
    (hbad : ¬HasBudgetedClique t G) (heven : ∀ v, Even (G.degree v))
    (hdef : degreeDeficiency G d<d)
    (hminimal : ∀ H : SimpleGraph (X ⊕ Fin 0),
      (∀ v, Even (H.degree v)) → degreeDeficiency H d<d → HasBudgetedClique t H)
    (hordered : ∀ i : Fin p, i.val≠0 →
      baseMissing G hp i≤p+(i.val+1)+prefixRho G hp (i.val+1)) :
    ∃ B : Finset X, B.Nonempty ∧ B.card<t ∧
      ∀ x∈B, missingNeighbors (G.comap (Sum.inl : X → X ⊕ Fin p))
        ((baseNeighbors G hp).erase x) x≤B.card+2*p+prefixRho G hp p := by
  have hc : 0<Fintype.card X := by
    have hn := G.degree_lt_card_verts (Sum.inr ⟨0,hp⟩)
    simp only [Fintype.card_sum,Fintype.card_fin] at hn
    omega
  letI : Nonempty X := Fintype.card_pos_iff.mp hc
  have hzero : ∀ A : GLWState G (prefixRho G hp) 0 (Nat.zero_le p), False :=
    GLWState.no_zero_of_minimality hp hbad heven hdef hminimal
  obtain ⟨j,hj,A,hstop⟩ := GLWState.exists_terminal hzero
  have hsize := A.clone_size_bound hp hpt hd hdegree hordered
  obtain ⟨W,hWnon,hWt,hWmiss⟩ := A.terminal_has_small_block hp hpt hbad heven hstop hsize
  let B := W.toFinset.image A.neighborExternal
  have hBcard : B.card=W.ncard := by
    rw [card_image_of_injective _ A.neighborExternal_injective,Set.toFinset_card]
    exact Nat.card_eq_fintype_card.symm
  have hBnon : B.Nonempty := by
    obtain ⟨u,hu⟩ := hWnon
    exact ⟨A.neighborExternal u,mem_image.mpr ⟨u,Set.mem_toFinset.mpr hu,rfl⟩⟩
  refine ⟨B,hBnon,hBcard ▸ hWt,?_⟩
  intro x hx
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  rw [hBcard]
  exact A.original_missing_block_bound hp W hWmiss hordered u (Set.mem_toFinset.mp hu)

end
end Cycle13
