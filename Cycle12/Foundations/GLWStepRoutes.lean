import Cycle12.Foundations.GLWState

/-! Reindex a concrete full suppression into the next prefix state. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PrefixVertices
theorem embedding_after_step {X : Type} {p j : ℕ} (h : j+1≤p) (v : X ⊕ Fin j) :
    embedding (Nat.le_trans (Nat.le_succ j) h) v=
      RoutedEdges.afterVertex (φ:=embedding h) (lastVertex j) (keep j v) := embedding_step h v

def survivingExternal {X : Type} (j : ℕ) : Set {v : X ⊕ Fin (j+1) // v≠lastVertex j} :=
  {v | v.val∈external (j+1)}

theorem keep_mem_survivingExternal {X : Type} {j : ℕ} (v : X ⊕ Fin j) :
    keep j v∈survivingExternal j ↔ v∈external j := keep_external_iff v

theorem survivingExternal_image {X : Type} (j : ℕ) :
    Subtype.val '' (survivingExternal (X:=X) j)=external (j+1) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩; exact hw
  · rintro ⟨x,rfl⟩
    exact ⟨keep j (Sum.inl x),⟨x,rfl⟩,rfl⟩

end PrefixVertices

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ} {hj : j+1≤p}
    (A : GLWState G rho (j+1) hj)
    (N : (⊤ : SimpleGraph (A.routes.Ports (lastVertex j))).Subgraph) (hN : N.IsMatching)

def stepped : RoutedEdges G (embedding (Nat.le_trans (Nat.le_succ j) hj))
    (Fin (Fintype.card ((A.routes.Kept (lastVertex j)) ⊕ N.edgeSet))) :=
  ((A.routes.suppress (lastVertex j) N hN).reindexVertices (keep j)
    (embedding (Nat.le_trans (Nat.le_succ j) hj)) (embedding_after_step hj)).normalize

theorem stepped_multiplicity (x y : X ⊕ Fin j) :
    (A.stepped N hN).multiplicity x y=
      (A.routes.suppress (lastVertex j) N hN).multiplicity (keep j x) (keep j y) := by
  rw [stepped,RoutedEdges.multiplicity_normalize,RoutedEdges.multiplicity_reindexVertices]

theorem stepped_degrees (hcover : N.verts=Set.univ) (v : X ⊕ Fin j) :
    (A.stepped N hN).degree v=G.degree (embedding (Nat.le_trans (Nat.le_succ j) hj) v) := by
  rw [stepped,RoutedEdges.degree_normalize,RoutedEdges.degree_reindexVertices,
    RoutedEdges.degree_suppress _ _ _ _ hcover,A.degrees,embedding_step hj]

theorem stepped_originals :
    G.comap (embedding (Nat.le_trans (Nat.le_succ j) hj))≤(A.stepped N hN).graph := by
  rw [stepped,RoutedEdges.graph_normalize,RoutedEdges.graph_reindexVertices]
  intro x y hxy
  apply A.routes.suppress_graph_contains (lastVertex j) N hN
  apply A.originals
  change G.Adj (embedding hj (keep j x).val) (embedding hj (keep j y).val)
  change G.Adj (embedding (Nat.le_trans (Nat.le_succ j) hj) x)
    (embedding (Nat.le_trans (Nat.le_succ j) hj) y) at hxy
  simpa only [← embedding_step hj] using hxy

theorem stepped_simple
    (hs : (A.routes.suppress (lastVertex j) N hN).SimpleOn (survivingExternal j)) :
    (A.stepped N hN).SimpleOn (external j) := by
  constructor
  · intro x hx
    rw [stepped_multiplicity]
    exact hs.1 _ ((keep_mem_survivingExternal x).mpr hx)
  · intro x hx y hy
    rw [stepped_multiplicity]
    exact hs.2 _ ((keep_mem_survivingExternal x).mpr hx) _ ((keep_mem_survivingExternal y).mpr hy)

theorem stepped_cross_unchanged
    (hc : ∀ x y, x∈survivingExternal j → y∉survivingExternal j →
      (A.routes.suppress (lastVertex j) N hN).multiplicity x y=A.routes.multiplicity x.val y.val)
    (x : X) (i : Fin j) : (A.stepped N hN).multiplicity (Sum.inl x) (Sum.inr i)=
      A.routes.multiplicity (Sum.inl x) (Sum.inr i.castSucc) := by
  rw [stepped_multiplicity,hc]
  · rfl
  · exact (keep_mem_survivingExternal _).mpr ⟨x,rfl⟩
  · simpa only [keep_mem_survivingExternal] using inr_not_mem_external (X:=X) j i

end GLWState
end
end Cycle13
