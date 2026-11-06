import Cycle12.Foundations.EvenRemainder
import Mathlib.Combinatorics.SimpleGraph.Operations

/-! An edge-minimal spanning subgraph of minimum degree d has an endpoint
of degree exactly d on every edge. This is the first reduction in DY Lemma 12. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem single_edge_degree_le_one (x y v : V) : (edge x y).degree v ≤ 1 := by
  have h := (edge x y).degree_le_card_edgeFinset (v:=v)
  have hc : (edge x y).edgeSet.ncard ≤ 1 := by
    have hh := Set.ncard_le_ncard (edgeSet_edge_subset (v:=x) (w:=y))
    simpa using hh
  apply h.trans
  simpa only [edgeFinset,Set.ncard_eq_toFinset_card'] using hc

theorem single_edge_degree_zero (x y v : V) (hx : v≠x) (hy : v≠y) :
    (edge x y).degree v=0 := by
  rw [← ncard_neighborSet]
  have he : (edge x y).neighborSet v=∅ := by
    ext w
    simp [mem_neighborSet,edge_adj,hx,hy]
  rw [he,Set.ncard_empty]

theorem erase_edge_preserves_min_degree (G : SimpleGraph V) {d : ℕ}
    (hmin : ∀ v, d ≤ G.degree v) {x y : V} (hxy : G.Adj x y)
    (hx : d < G.degree x) (hy : d < G.degree y) :
    ∀ v, d ≤ (G\edge x y).degree v := by
  intro v
  have hb := degree_sdiff_add G (edge x y) (G.edge_le_iff.mpr (Or.inr hxy)) v
  have hl := single_edge_degree_le_one x y v
  by_cases hvx : v=x
  · subst v
    simp only [← ncard_neighborSet] at hb hl hx ⊢
    omega
  by_cases hvy : v=y
  · subst v
    simp only [← ncard_neighborSet] at hb hl hy ⊢
    omega
  have hz := single_edge_degree_zero x y v hvx hvy
  have hm := hmin v
  simp only [← ncard_neighborSet] at hb hz hm ⊢
  omega

theorem exists_edge_minimal_min_degree (G : SimpleGraph V) {d : ℕ}
    (hmin : ∀ v, d ≤ G.degree v) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ v, d ≤ H.degree v) ∧
      ∀ x y, H.Adj x y → H.degree x=d ∨ H.degree y=d := by
  have hex : ∃ n : ℕ, ∃ H : SimpleGraph V,
      H.edgeSet.ncard=n ∧ H ≤ G ∧ ∀ v, d ≤ H.degree v :=
    ⟨G.edgeSet.ncard,G,rfl,le_rfl,hmin⟩
  obtain ⟨H,hcard,hHG,hdeg⟩ := Nat.find_spec hex
  refine ⟨H,hHG,hdeg,?_⟩
  intro x y hxy
  by_contra! hn
  have hx : d < H.degree x := lt_of_le_of_ne (hdeg x) hn.1.symm
  have hy : d < H.degree y := lt_of_le_of_ne (hdeg y) hn.2.symm
  have hnew := erase_edge_preserves_min_degree H hdeg hxy hx hy
  have hlt : (H\edge x y).edgeSet.ncard < H.edgeSet.ncard := by
    rw [edgeSet_sdiff,edgeSet_edge_of_ne hxy.ne]
    have he : s(x,y)∈H.edgeSet := H.mem_edgeSet.mpr hxy
    have hh := Set.ncard_sdiff_singleton_add_one he
    omega
  have hle := Nat.find_min' hex (show ∃ K : SimpleGraph V,
    K.edgeSet.ncard=(H\edge x y).edgeSet.ncard ∧ K ≤ G ∧ ∀ v, d ≤ K.degree v from
      ⟨H\edge x y,rfl,sdiff_le.trans hHG,by
        simpa only [← ncard_neighborSet] using hnew⟩)
  omega

end
end Cycle13
