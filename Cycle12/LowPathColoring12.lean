import Cycle12.Foundations.ColorExtension
import Cycle12.BoundedDemandGroups12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def lowPathConflict (a b z : I → V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ (a i=a j ∨ a i=b j ∨ b i=a j ∨ b i=b j ∨ z i=z j)
  symm := ⟨by intro i j h; exact ⟨h.1.symm,by rcases h.2 with h|h|h|h|h <;> simp_all [eq_comm]⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

/-- Counting conflicts removes the path itself from each of its three
incidence lists. The resulting palette has no extra rounding unit. -/
theorem lowPathConflict_degree (a b z : I → V) {A D : ℕ}
    (hend : ∀ v,(univ.filter (fun i => a i=v ∨ b i=v)).card ≤ A)
    (hcenter : ∀ v,(univ.filter (fun i => z i=v)).card ≤ D) (i : I) :
    (lowPathConflict a b z).degree i+3 ≤ 2*A+D := by
  let S := univ.filter (fun j => a j=a i ∨ b j=a i)
  let T := univ.filter (fun j => a j=b i ∨ b j=b i)
  let Z := univ.filter (fun j => z j=z i)
  have hiS : i∈S := by simp [S]
  have hiT : i∈T := by simp [T]
  have hiZ : i∈Z := by simp [Z]
  have hs : (lowPathConflict a b z).neighborFinset i ⊆ S.erase i∪T.erase i∪Z.erase i := by
    intro j hj
    have h : i ≠ j ∧ (a i=a j ∨ a i=b j ∨ b i=a j ∨ b i=b j ∨ z i=z j) :=
      (mem_neighborFinset _ _ _).mp hj
    simp only [mem_union,mem_erase,S,T,Z,mem_filter,mem_univ,true_and]
    rcases h.2 with h'|h'|h'|h'|h'
    · exact Or.inl (Or.inl ⟨h.1.symm,Or.inl h'.symm⟩)
    · exact Or.inl (Or.inl ⟨h.1.symm,Or.inr h'.symm⟩)
    · exact Or.inl (Or.inr ⟨h.1.symm,Or.inl h'.symm⟩)
    · exact Or.inl (Or.inr ⟨h.1.symm,Or.inr h'.symm⟩)
    · exact Or.inr ⟨h.1.symm,h'.symm⟩
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have hc' := card_union_le (S.erase i) (T.erase i)
  have hS := card_erase_add_one hiS
  have hT := card_erase_add_one hiT
  have hZ := card_erase_add_one hiZ
  have hSa := hend (a i)
  have hTb := hend (b i)
  have hZz := hcenter (z i)
  rw [card_neighborFinset_eq_degree] at hc
  change S.card ≤ A at hSa
  change T.card ≤ A at hTb
  change Z.card ≤ D at hZz
  omega

theorem low_path_coloring (a b z : I → V) {A D : ℕ} (hpalette : 0<2*A+D)
    (hend : ∀ v,(univ.filter (fun i => a i=v ∨ b i=v)).card ≤ A)
    (hcenter : ∀ v,(univ.filter (fun i => z i=v)).card ≤ D) :
    Nonempty ((lowPathConflict a b z).Coloring (Fin (2*A+D))) := by
  obtain ⟨f,_⟩ := exists_coloring_extension (lowPathConflict a b z) ∅
    (fun _ => (⟨0,hpalette⟩ : Fin (2*A+D))) (by simp) (by
      intro i
      have hh := lowPathConflict_degree a b z hend hcenter i
      rw [Fintype.card_fin]
      omega)
  exact ⟨f⟩

theorem low_path_same_color_disjoint (a b z : I → V) (U : Finset V)
    (ha : ∀ i,a i∈U) (hb : ∀ i,b i∈U) (hz : ∀ i,z i∉U)
    {C : Type} (color : (lowPathConflict a b z).Coloring C)
    {i j : I} (hij : i ≠ j) (hc : color i=color j) :
    Disjoint ({a i,b i,z i}:Finset V) {a j,b j,z j} := by
  have hn : ¬(a i=a j ∨ a i=b j ∨ b i=a j ∨ b i=b j ∨ z i=z j) :=
    fun hh => color.valid ⟨hij,hh⟩ hc
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [mem_insert,mem_singleton] at hv hw
  rcases hv with rfl|rfl|rfl <;> rcases hw with h|h|h
  · exact hn (Or.inl h)
  · exact hn (Or.inr (Or.inl h))
  · exact hz j (h ▸ ha i)
  · exact hn (Or.inr (Or.inr (Or.inl h)))
  · exact hn (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hz j (h ▸ hb i)
  · exact hz i (h.symm ▸ ha j)
  · exact hz i (h.symm ▸ hb j)
  · exact hn (Or.inr (Or.inr (Or.inr (Or.inr h))))

end
end Cycle12
