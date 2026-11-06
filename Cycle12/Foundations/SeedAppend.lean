import Cycle12.Foundations.OrderedSeed

/-! Append new vertices to an ordered embedding. Prefix counts and the
remaining neighbor reservoir are computed exactly. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def appendVertices {V : Type} {p q : ℕ} (a : Fin p ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i≠b j) : Fin (p+q) ↪ V :=
  finSumFinEquiv.symm.toEmbedding.trans {
    toFun := Sum.elim a b
    inj' := by
      rintro (i | j) (k | l) h
      · exact congrArg Sum.inl (a.injective h)
      · exact False.elim (hd i l h)
      · exact False.elim (hd k j h.symm)
      · exact congrArg Sum.inr (b.injective h) }

@[simp] theorem appendVertices_left {V : Type} {p q : ℕ} (a : Fin p ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i≠b j) (i : Fin p) : appendVertices a b hd (i.castAdd q)=a i := by
  simp [appendVertices]
  rfl

@[simp] theorem appendVertices_right {V : Type} {p q : ℕ} (a : Fin p ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i≠b j) (i : Fin q) : appendVertices a b hd (i.natAdd p)=b i := by
  simp [appendVertices]
  rfl

theorem appendVertices_image {V : Type} [DecidableEq V] {p q : ℕ}
    (a : Fin p ↪ V) (b : Fin q ↪ V) (hd : ∀ i j, a i≠b j) :
    univ.image (appendVertices a b hd)=univ.image a ∪ univ.image b := by
  ext v
  simp only [mem_image,mem_univ,true_and,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨s,rfl⟩ := finSumFinEquiv.surjective i
    cases s with
    | inl i => exact Or.inl ⟨i,by simpa using hi⟩
    | inr i => exact Or.inr ⟨i,by simpa using hi⟩
  · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact ⟨i.castAdd q,appendVertices_left a b hd i⟩
    · exact ⟨i.natAdd p,appendVertices_right a b hd i⟩

theorem seedReservoir_append {V : Type} [Fintype V] [DecidableEq V] {p q : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i≠b j) :
    seedReservoir G root (appendVertices a b hd)=seedReservoir G root a \ univ.image b := by
  rw [seedReservoir,appendVertices_image,seedReservoir]
  ext v
  simp [and_assoc]

theorem seedRho_append_formula {V : Type} {p q : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i≠b j) (k : ℕ) :
    seedRho G root (appendVertices a b hd) k=
      seedRho G root a k+∑ i : Fin q, if p+i.val<k ∧ ¬G.Adj root (b i) then (1:ℕ) else 0 := by
  have hs : seedRho G root (appendVertices a b hd) k=
      ∑ s : Fin p ⊕ Fin q, if (finSumFinEquiv s).val<k ∧
        ¬G.Adj root (appendVertices a b hd (finSumFinEquiv s)) then (1:ℕ) else 0 := by
    have hcount : seedRho G root (appendVertices a b hd) k=
        ∑ i, if i.val<k ∧ ¬G.Adj root (appendVertices a b hd i) then (1:ℕ) else 0 := by
      simp [seedRho]
    rw [hcount]
    exact (Fintype.sum_equiv finSumFinEquiv _ _ (fun _ => rfl)).symm
  rw [hs,Fintype.sum_sum_type]
  simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
    appendVertices_left,appendVertices_right,Fin.val_castAdd,Fin.val_natAdd]
  congr 1
  simp [seedRho]

theorem seedRho_append_prefix {V : Type} {p q k : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i≠b j) (hk : k≤p) :
    seedRho G root (appendVertices a b hd) k=seedRho G root a k := by
  rw [seedRho_append_formula]
  have hz : ∀ i : Fin q, ¬(p+i.val<k ∧ ¬G.Adj root (b i)) := by intro i h; omega
  simp only [hz,if_false,sum_const_zero,Nat.add_zero]

theorem seedRho_append_lower {V : Type} {p q k : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i≠b j) (hk : p≤k) :
    seedRho G root a p ≤ seedRho G root (appendVertices a b hd) k := by
  rw [seedRho_append_formula]
  exact (seedRho_monotone G root a hk).trans (Nat.le_add_right _ _)

end
end Cycle13
