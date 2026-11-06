import Cycle12.Foundations.GLWNearStep

/-! The actual prefix count of vertices nonadjacent to the first ordered
vertex, including that first vertex itself. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

def prefixRho {X : Type} {p : ℕ} (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) (j : ℕ) : ℕ :=
  (univ.filter (fun i : Fin p => i.val<j ∧ ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i))).card

theorem prefixRho_monotone {X : Type} {p : ℕ} (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) :
    Monotone (prefixRho G hp) := by
  intro a b hab
  apply card_le_card
  intro i hi
  have h := (mem_filter.mp hi).2
  exact mem_filter.mpr ⟨mem_univ _,h.1.trans_le hab,h.2⟩

theorem prefixRho_le {X : Type} {p : ℕ} (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) (j : ℕ) :
    prefixRho G hp j≤j := by
  let S := univ.filter (fun i : Fin p => i.val<j ∧ ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i))
  let f : S → Fin j := fun i => ⟨i.val.val,(mem_filter.mp i.property).2.1⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Fin.ext (congrArg (fun i : Fin j => i.val) h))
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fin,S,prefixRho] using h

theorem prefixRho_succ_of_not_adj {X : Type} {p j : ℕ}
    (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) (hj : j<p)
    (hn : ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr ⟨j,hj⟩)) :
    prefixRho G hp (j+1)=prefixRho G hp j+1 := by
  let k : Fin p := ⟨j,hj⟩
  let S := univ.filter (fun i : Fin p => i.val<j ∧ ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i))
  have he : univ.filter (fun i : Fin p => i.val<j+1 ∧ ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i))=
      insert k S := by
    ext i
    simp only [S,mem_filter,mem_univ,true_and,mem_insert]
    change (i.val<j+1 ∧ ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i)) ↔
      i=k ∨ (i.val<j ∧ ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i))
    by_cases hi : i=k
    · subst i
      simp [k,hn]
    · have hiv : i.val≠j := fun h => hi (Fin.ext h)
      simp only [hi,false_or]
      constructor <;> rintro ⟨hlt,hadj⟩ <;> exact ⟨by omega,hadj⟩
  have hk : k∉S := by simp [S,k]
  unfold prefixRho
  rw [he,card_insert_of_notMem hk]

end
end Cycle13
