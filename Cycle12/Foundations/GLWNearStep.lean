import Cycle12.Foundations.GLWWellStep

/-! All GLW state invariants survive the one-edge crossing increment. Only
the selected external vertex enters the history set; no ownership history is used. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ} {hj : j+1≤p}
    (A : GLWState G rho (j+1) hj)

def nearStep (N : (⊤ : SimpleGraph (A.routes.Ports (lastVertex j))).Subgraph)
    (hN : N.IsMatching) (hcover : N.verts=Set.univ)
    (hs : (A.routes.suppress (lastVertex j) N hN).SimpleOn (survivingExternal j))
    (x₀ : X) (s : Fin j) (hfresh : x₀∉A.used)
    (hc : ∀ x i, (A.stepped N hN).multiplicity (Sum.inl x) (Sum.inr i)=
      A.routes.multiplicity (Sum.inl x) (Sum.inr i.castSucc)+(if x=x₀ ∧ i=s then 1 else 0))
    (hrho : rho j≤rho (j+1)) (hmax : rho (j+1)≤rho p)
    (hinc : s.val≠0 → rho (j+1)=rho j+1) :
    GLWState G rho j (Nat.le_trans (Nat.le_succ j) hj) where
  edgeCount := _
  routes := A.stepped N hN
  used := insert x₀ A.used
  degrees := A.stepped_degrees N hN hcover
  originals := A.stepped_originals N hN
  external_simple := A.stepped_simple N hN hs
  crossing := by
    intro x i
    rw [hc]
    by_cases he : x=x₀ ∧ i=s
    · rw [if_pos he]
      have hh := A.fresh_crossing_le_one hfresh i.castSucc
      rw [he.1]
      omega
    · rw [if_neg he,Nat.add_zero]
      exact A.crossing x i.castSucc
  doubles := by
    intro i
    have hh := A.doubles i.castSucc
    change _≤(if i.val=0 then p-(j+1) else rho p-rho (j+1)) at hh
    by_cases his : i=s
    · subst i
      have hsub : univ.filter (fun x : X => (A.stepped N hN).multiplicity (Sum.inl x) (Sum.inr s)=2) ⊆
          insert x₀ (univ.filter (fun x : X => A.routes.multiplicity (Sum.inl x) (Sum.inr s.castSucc)=2)) := by
        intro x hx
        by_cases hxe : x=x₀
        · exact mem_insert.mpr (Or.inl hxe)
        · apply mem_insert_of_mem
          have hm := (mem_filter.mp hx).2
          rw [hc,if_neg (fun h => hxe h.1),Nat.add_zero] at hm
          exact mem_filter.mpr ⟨mem_univ _,hm⟩
      have hcard := (card_le_card hsub).trans (card_insert_le _ _)
      by_cases hs0 : s.val=0
      · simp only [hs0,if_true] at hh ⊢
        omega
      · simp only [hs0,if_false] at hh ⊢
        have hi := hinc hs0
        omega
    · have he : univ.filter (fun x : X => (A.stepped N hN).multiplicity (Sum.inl x) (Sum.inr i)=2)=
          univ.filter (fun x : X => A.routes.multiplicity (Sum.inl x) (Sum.inr i.castSucc)=2) := by
        ext x
        simp [hc,his]
      rw [he]
      by_cases hi : i.val=0
      · simp only [hi,if_true] at hh ⊢
        omega
      · simp only [hi,if_false] at hh ⊢
        exact hh.trans (Nat.sub_le_sub_left hrho (rho p))
  double_used := by
    intro x i h
    by_cases he : x=x₀
    · exact mem_insert.mpr (Or.inl he)
    · apply mem_insert_of_mem
      rw [hc,if_neg (fun hh => he hh.1),Nat.add_zero] at h
      exact A.double_used x i.castSucc h
  used_card := by
    have h := A.used_card
    have hi := card_insert_le x₀ A.used
    omega

end GLWState
end
end Cycle13
