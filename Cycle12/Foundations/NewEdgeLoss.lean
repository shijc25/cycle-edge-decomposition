import Cycle12.Foundations.ImmersionPaths
import Cycle12.Foundations.OrderedLinks

/-! The missing-edge pullback bound in GLW Claim 3.8. Every new edge at a
retained vertex consumes a distinct original edge to a deleted vertex. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma first_edge_of_walk {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hne : u ≠ v) :
    ∃ w, G.Adj u w ∧ w ∈ p.support ∧ s(u,w) ∈ p.edgeSet := by
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons h p => exact ⟨_,h,by simp,by simp⟩

namespace EdgeRouting
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {H : SimpleGraph V} {G : SimpleGraph W} (R : EdgeRouting H G)

theorem new_adjacencies_le_deleted (v : V) :
    (univ.filter (fun w => H.Adj v w ∧ ¬G.Adj (R.vertex v) (R.vertex w))).card ≤
      Fintype.card W-Fintype.card V := by
  classical
  let S := univ.filter (fun w => H.Adj v w ∧ ¬G.Adj (R.vertex v) (R.vertex w))
  let D := univ \ univ.image R.vertex
  have hex : ∀ w : S, ∃ x : D, s(R.vertex v,x.val) ∈
      (R.route (mem_filter.mp w.property).2.1).edgeSet := by
    intro w
    have hw := (mem_filter.mp w.property).2
    obtain ⟨x,hx,hxs,hxe⟩ := first_edge_of_walk (R.route hw.1) (R.vertex.injective.ne hw.1.ne)
    have hxD : x ∈ D := by
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      rintro hximage
      obtain ⟨u,_,hu⟩ := mem_image.mp hximage
      have huS : R.vertex u ∈ (R.route hw.1).support := hu ▸ hxs
      rcases R.avoids hw.1 u huS with rfl | rfl
      · exact G.irrefl (by simpa only [← hu] using hx)
      · exact hw.2 (by simpa only [← hu] using hx)
    exact ⟨⟨x,hxD⟩,hxe⟩
  let f : S → D := fun w => (hex w).choose
  have hf : Function.Injective f := by
    intro a b heq
    by_contra hab
    have hne : s(v,a.val) ≠ s(v,b.val) := by
      intro he
      exact hab (Subtype.ext (Sym2.congr_right.mp he))
    have hd := R.disjoint (mem_filter.mp a.property).2.1 (mem_filter.mp b.property).2.1 hne
    have ha := (hex a).choose_spec
    have hb := (hex b).choose_spec
    have he : (hex a).choose.val=(hex b).choose.val := congrArg Subtype.val heq
    rw [← he] at hb
    exact Set.disjoint_left.mp hd ha hb
  have hc : S.card ≤ D.card := card_le_card_of_injective hf
  have hD : D.card=Fintype.card W-Fintype.card V := by
    dsimp [D]
    rw [card_sdiff_of_subset (subset_univ _),card_univ,
      card_image_of_injective _ R.vertex.injective,card_univ]
  exact hD ▸ hc

theorem missing_pullback_le (B : Finset V) (v : V) :
    missingNeighbors (G.comap R.vertex) B v ≤ missingNeighbors H B v +
      (Fintype.card W-Fintype.card V) := by
  classical
  let S := univ.filter (fun w => H.Adj v w ∧ ¬G.Adj (R.vertex v) (R.vertex w))
  have hs : B.filter (fun w => ¬ (G.comap R.vertex).Adj v w) ⊆
      B.filter (fun w => ¬H.Adj v w) ∪ S := by
    intro w hw
    have hw' := mem_filter.mp hw
    by_cases hH : H.Adj v w
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hH,hw'.2⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hw'.1,hH⟩)
  have h₁ := card_le_card hs
  have h₂ := card_union_le (B.filter (fun w => ¬H.Adj v w)) S
  have h₃ := R.new_adjacencies_le_deleted v
  change S.card ≤ Fintype.card W-Fintype.card V at h₃
  have hleft : missingNeighbors (G.comap R.vertex) B v =
      (B.filter (fun w => ¬ (G.comap R.vertex).Adj v w)).card := by
    unfold missingNeighbors
    congr 1
  have hright : missingNeighbors H B v=(B.filter (fun w => ¬H.Adj v w)).card := by
    unfold missingNeighbors
    congr 1
  rw [hleft,hright]
  omega

end EdgeRouting
end
end Cycle13
