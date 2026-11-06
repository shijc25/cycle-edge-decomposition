import Cycle12.Foundations.PrefixVertices

/-! The controlled GLW suppression state. A set covering current external
double-edge endpoints replaces the stronger historical owner invariant; the missing-edge
pullback is already proved directly from original host paths. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

structure GLWStateData {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (G : SimpleGraph (X ⊕ Fin p)) (rho : ℕ → ℕ) (j : ℕ)
    (φ : X ⊕ Fin j ↪ X ⊕ Fin p) where
  edgeCount : ℕ
  routes : RoutedEdges G φ (Fin edgeCount)
  used : Finset X
  degrees : ∀ v, routes.degree v=G.degree (φ v)
  originals : G.comap φ ≤ routes.graph
  external_simple : routes.SimpleOn (PrefixVertices.external j)
  crossing : ∀ x i, routes.multiplicity (Sum.inl x) (Sum.inr i)≤2
  doubles : ∀ i : Fin j,
    (univ.filter (fun x : X => routes.multiplicity (Sum.inl x) (Sum.inr i)=2)).card≤
      (if i.val=0 then p-j else rho p-rho j)
  double_used : ∀ x i, routes.multiplicity (Sum.inl x) (Sum.inr i)=2 → x∈used
  used_card : used.card≤p-j

abbrev GLWState {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (G : SimpleGraph (X ⊕ Fin p)) (rho : ℕ → ℕ) (j : ℕ) (hj : j≤p) :=
  GLWStateData G rho j (PrefixVertices.embedding hj)

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ}

def initial (G : SimpleGraph (X ⊕ Fin p)) (rho : ℕ → ℕ) : GLWState G rho p (Nat.le_refl p) := by
  have hemb := PrefixVertices.embedding_full (X:=X) (p:=p)
  let R := (RoutedEdges.original G).normalize
  have hs : R.IsSimple := by
    apply R.isSimple_iff_multiplicity.mpr
    have h := (RoutedEdges.original G).isSimple_iff_multiplicity.mp (RoutedEdges.original_simple G)
    constructor
    · intro x; rw [RoutedEdges.multiplicity_normalize]; exact h.1 x
    · intro x y; rw [RoutedEdges.multiplicity_normalize]; exact h.2 x y
  have hr : R.graph=G := by rw [RoutedEdges.graph_normalize,RoutedEdges.original_graph]
  have hm := R.isSimple_iff_multiplicity.mp hs
  have htwo : ∀ x i, R.multiplicity (Sum.inl x) (Sum.inr i)≠2 := by
    intro x i
    have h := hm.2 (Sum.inl x) (Sum.inr i)
    omega
  change GLWStateData G rho p _
  rw [hemb]
  refine ⟨_,R,∅,?_,?_,?_,?_,?_,?_,?_⟩
  · intro v
    exact (RoutedEdges.degree_normalize _ v).trans (RoutedEdges.original_degree G v)
  · intro u v huv
    rw [hr]
    exact huv
  · exact ⟨fun x _ => hm.1 x,fun x _ y _ => hm.2 x y⟩
  · intro x i; exact (hm.2 _ _).trans (by decide)
  · intro i
    have he : univ.filter (fun x : X => R.multiplicity (Sum.inl x) (Sum.inr i)=2)=∅ := by
      ext x
      simp [htwo x i]
    rw [he,card_empty]
    exact Nat.zero_le _
  · intro x i h; exact False.elim (htwo x i h)
  · simp

theorem fresh_crossing_le_one {hj : j≤p} (A : GLWState G rho j hj)
    {x : X} (hx : x∉A.used) (i : Fin j) : A.routes.multiplicity (Sum.inl x) (Sum.inr i)≤1 := by
  have hu := A.crossing x i
  have hn : A.routes.multiplicity (Sum.inl x) (Sum.inr i)≠2 := fun h => hx (A.double_used x i h)
  omega

theorem zero_simple (A : GLWState G rho 0 (Nat.zero_le p)) : A.routes.IsSimple := by
  apply (A.routes.simpleOn_univ_iff).mp
  have he : PrefixVertices.external (X:=X) 0=Set.univ := by
    ext v
    cases v with
    | inl x => simp
    | inr i => exact Fin.elim0 i
  have h := A.external_simple
  rwa [he] at h

end GLWState
end
end Cycle13
