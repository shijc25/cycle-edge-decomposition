import Cycle12.Foundations.GLWStepRoutes

/-! Preservation of every GLW state invariant in the well-suppression case. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ} {hj : j+1≤p}
    (A : GLWState G rho (j+1) hj)

def wellStep (N : (⊤ : SimpleGraph (A.routes.Ports (lastVertex j))).Subgraph)
    (hN : N.IsMatching) (hcover : N.verts=Set.univ)
    (hs : (A.routes.suppress (lastVertex j) N hN).SimpleOn (survivingExternal j))
    (hc : ∀ x y, x∈survivingExternal j → y∉survivingExternal j →
      (A.routes.suppress (lastVertex j) N hN).multiplicity x y=A.routes.multiplicity x.val y.val)
    (hrho : rho j≤rho (j+1)) : GLWState G rho j (Nat.le_trans (Nat.le_succ j) hj) where
  edgeCount := _
  routes := A.stepped N hN
  used := A.used
  degrees := A.stepped_degrees N hN hcover
  originals := A.stepped_originals N hN
  external_simple := A.stepped_simple N hN hs
  crossing := by
    intro x i
    rw [A.stepped_cross_unchanged N hN hc]
    exact A.crossing x i.castSucc
  doubles := by
    intro i
    have hh := A.doubles i.castSucc
    have he : univ.filter (fun x : X => (A.stepped N hN).multiplicity (Sum.inl x) (Sum.inr i)=2)=
        univ.filter (fun x : X => A.routes.multiplicity (Sum.inl x) (Sum.inr i.castSucc)=2) := by
      ext x
      simp only [mem_filter,mem_univ,true_and,A.stepped_cross_unchanged N hN hc]
    rw [he]
    change _≤(if i.val=0 then p-(j+1) else rho p-rho (j+1)) at hh
    by_cases hi : i.val=0
    · simp only [hi,if_true] at hh ⊢
      omega
    · simp only [hi,if_false] at hh ⊢
      exact hh.trans (Nat.sub_le_sub_left hrho (rho p))
  double_used := by
    intro x i h
    rw [A.stepped_cross_unchanged N hN hc] at h
    exact A.double_used x i.castSucc h
  used_card := by
    have h := A.used_card
    omega

end GLWState
end
end Cycle13
