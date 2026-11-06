import Cycle12.Foundations.MinimalDegree
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Hall allocation of distinct low-degree neighbours to the high-degree
vertices of an edge-minimal minimum-degree graph. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem high_vertices_independent (G : SimpleGraph V) {d : ℕ}
    (hends : ∀ x y, G.Adj x y → G.degree x=d ∨ G.degree y=d)
    {x y : V} (hx : d < G.degree x) (hy : d < G.degree y) : ¬G.Adj x y := by
  intro hxy
  rcases hends x y hxy with hh | hh <;> omega

theorem exists_distinct_high_neighbors (G : SimpleGraph V) {d : ℕ} (hd : 0<d)
    (hends : ∀ x y, G.Adj x y → G.degree x=d ∨ G.degree y=d)
    (A : Finset V) (hA : ∀ x ∈ A, d < G.degree x) :
    ∃ g : A ↪ V, ∀ x : A, G.Adj x.val (g x) ∧ G.degree (g x)=d := by
  let N : A → Finset V := fun x => G.neighborFinset x.val
  have hall : ∀ S : Finset A, S.card ≤ (S.biUnion N).card := by
    intro S
    let B := S.biUnion N
    have hleft : ∀ x∈S, d ≤ (B.bipartiteAbove (fun a : A => G.Adj a.val) x).card := by
      intro x hx
      have he : B.bipartiteAbove (fun a : A => G.Adj a.val) x=N x := by
        ext y
        simp only [mem_bipartiteAbove]
        constructor
        · exact fun h => (G.mem_neighborFinset x.val y).mpr h.2
        · intro hy
          exact ⟨mem_biUnion.mpr ⟨x,hx,hy⟩,(G.mem_neighborFinset x.val y).mp hy⟩
      rw [he]
      change d ≤ (G.neighborFinset x.val).card
      rw [card_neighborFinset_eq_degree]
      exact (hA x x.property).le
    have hright : ∀ y∈B, (S.bipartiteBelow (fun a : A => G.Adj a.val) y).card ≤ d := by
      intro y hy
      obtain ⟨x,hx,hxy⟩ := mem_biUnion.mp hy
      have hxy' : G.Adj x.val y := (G.mem_neighborFinset x.val y).mp hxy
      have hdy : G.degree y=d := (hends _ _ hxy').resolve_left (Nat.ne_of_gt (hA x x.property))
      let C := S.bipartiteBelow (fun a : A => G.Adj a.val) y
      have hs : C.image Subtype.val ⊆ G.neighborFinset y := by
        rintro z hz
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
        exact (G.mem_neighborFinset y a.val).mpr ((mem_bipartiteBelow (fun a : A => G.Adj a.val)).mp ha).2.symm
      have hh := card_le_card hs
      rw [card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree,hdy] at hh
      exact hh
    have hh := card_nsmul_le_card_nsmul (R:=ℕ) (fun a : A => G.Adj a.val) hleft hright
    simp only [smul_eq_mul] at hh
    exact le_of_mul_le_mul_right hh hd
  obtain ⟨g,hg,hgN⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  refine ⟨⟨g,hg⟩,fun x => ?_⟩
  have ha : G.Adj x.val (g x) := (G.mem_neighborFinset x.val (g x)).mp (hgN x)
  exact ⟨ha,(hends _ _ ha).resolve_left (Nat.ne_of_gt (hA x x.property))⟩

end
end Cycle13
