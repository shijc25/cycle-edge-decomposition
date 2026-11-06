import Cycle12.Foundations.RoutedReindex

/-! Fixed vertex types for suppressing the ordered vertices from last to first. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PrefixVertices
variable {X : Type} {p j : ℕ}

def embedding (h : j≤p) : X ⊕ Fin j ↪ X ⊕ Fin p where
  toFun := Sum.map id (Fin.castLE h)
  inj' := by
    rintro (x | i) (y | k) he
    · exact congrArg Sum.inl (Sum.inl.inj he)
    · exact False.elim (Sum.inl_ne_inr he)
    · exact False.elim (Sum.inr_ne_inl he)
    · apply congrArg Sum.inr
      apply Fin.ext
      have he' : Fin.castLE h i=Fin.castLE h k := Sum.inr.inj he
      exact congrArg (fun a : Fin p => a.val) he'

@[simp] theorem embedding_inl (h : j≤p) (x : X) : embedding h (Sum.inl x)=Sum.inl x := rfl
@[simp] theorem embedding_inr (h : j≤p) (i : Fin j) :
    embedding (X:=X) h (Sum.inr i)=Sum.inr (Fin.castLE h i) := rfl

theorem embedding_full : embedding (X:=X) (Nat.le_refl p)=Function.Embedding.refl _ := by
  ext (x | i) <;> rfl

def lastVertex (j : ℕ) : X ⊕ Fin (j+1) := Sum.inr (Fin.last j)

def keep (j : ℕ) : X ⊕ Fin j ≃ {v : X ⊕ Fin (j+1) // v≠lastVertex j} where
  toFun := fun v => match v with
    | .inl x => ⟨.inl x,Sum.inl_ne_inr⟩
    | .inr i => ⟨.inr i.castSucc,fun h => i.castSucc_ne_last (Sum.inr.inj h)⟩
  invFun := fun v => match v with
    | ⟨.inl x,_⟩ => .inl x
    | ⟨.inr i,h⟩ => .inr (i.castPred (fun he => h (congrArg Sum.inr he)))
  left_inv := by
    rintro (x | i)
    · rfl
    · change Sum.inr (i.castSucc.castPred _)=Sum.inr i
      rw [Fin.castPred_castSucc]
  right_inv := by
    rintro ⟨x | i,h⟩
    · rfl
    · apply Subtype.ext
      change Sum.inr ((i.castPred _).castSucc)=Sum.inr i
      rw [Fin.castSucc_castPred]

@[simp] theorem keep_inl (j : ℕ) (x : X) : (keep j (Sum.inl x)).val=Sum.inl x := rfl
@[simp] theorem keep_inr (j : ℕ) (i : Fin j) :
    (keep (X:=X) j (Sum.inr i)).val=Sum.inr i.castSucc := rfl

theorem embedding_step (h : j+1≤p) (v : X ⊕ Fin j) :
    embedding (Nat.le_trans (Nat.le_succ j) h) v=
      embedding h (keep j v).val := by
  cases v <;> rfl

def external (j : ℕ) : Set (X ⊕ Fin j) := Set.range Sum.inl

theorem mem_external_iff (v : X ⊕ Fin j) : v∈external j ↔ ∃ x, Sum.inl x=v := Iff.rfl

@[simp] theorem inl_mem_external (j : ℕ) (x : X) : Sum.inl x∈external j := ⟨x,rfl⟩
@[simp] theorem inr_not_mem_external (j : ℕ) (i : Fin j) :
    Sum.inr i∉external (X:=X) j := by rintro ⟨x,h⟩; exact Sum.inl_ne_inr h

theorem keep_external_iff (v : X ⊕ Fin j) :
    (keep j v).val∈external (j+1) ↔ v∈external j := by
  cases v <;> simp

end PrefixVertices
end
end Cycle13
