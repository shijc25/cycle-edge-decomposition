import Cycle12.HBaseApplication
import Cycle12.TwinReduction

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type}

def HSpoke (G : SimpleGraph V) (f : Fin 5 ↪ V) (k : Fin 5) (x : V) : Prop :=
  (∀ i, x≠f i) ∧ ∀ v, G.Adj x v ↔ v=f 0 ∨ v=f k

/-- The four finite H residue cases apply whenever no spoke class contains
two distinct vertices. All choices of core chords are already covered. -/
theorem terminal_h_without_twins [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : Fin 5 ↪ V) (hf : HFrame G f)
    (hunique : ∀ k : Fin 5, k=2 ∨ k=3 → ∀ x y,
      HSpoke G f k x → HSpoke G f k y → x=y) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hcover : ∀ v, (∃ i, f i=v) ∨ HSpoke G f 2 v ∨ HSpoke G f 3 v := by
    intro v
    by_cases hv : ∃ i, f i=v
    · exact Or.inl hv
    · have hvo : ∀ i, v≠f i := fun i he => hv ⟨i,he.symm⟩
      rcases hf.2 v hvo with h | h
      · exact Or.inr (Or.inl ⟨hvo,h⟩)
      · exact Or.inr (Or.inr ⟨hvo,h⟩)
  by_cases hA : ∃ x, HSpoke G f 2 x
  · obtain ⟨x,hx⟩ := hA
    by_cases hB : ∃ y, HSpoke G f 3 y
    · obtain ⟨y,hy⟩ := hB
      have hxy : x≠y := by
        intro he
        subst y
        exact h_frame_types_disjoint f x hx.2 hy.2
      apply terminal_h_base11 G f hf.1 x hx.1 hx.2 y hy.1 hy.2 hxy
      intro v
      rcases hcover v with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hunique 2 (Or.inl rfl) v x h hx))
      · exact Or.inr (Or.inr (hunique 3 (Or.inr rfl) v y h hy))
    · apply terminal_h_base10 G f hf.1 x hx.1 hx.2
      intro v
      rcases hcover v with h | h | h
      · exact Or.inl h
      · exact Or.inr (hunique 2 (Or.inl rfl) v x h hx)
      · exact False.elim (hB ⟨v,h⟩)
  · by_cases hB : ∃ y, HSpoke G f 3 y
    · obtain ⟨y,hy⟩ := hB
      apply terminal_h_base01 G f hf.1 y hy.1 hy.2
      intro v
      rcases hcover v with h | h | h
      · exact Or.inl h
      · exact False.elim (hA ⟨v,h⟩)
      · exact Or.inr (hunique 3 (Or.inr rfl) v y h hy)
    · apply terminal_h_base00 G f hf.1
      intro v
      rcases hcover v with h | h | h
      · exact h
      · exact False.elim (hA ⟨v,h⟩)
      · exact False.elim (hB ⟨v,h⟩)

/-- An unconditional terminal bound for the entire infinite H family,
with arbitrary core chords. Repeated twin removal reaches exactly one of
the four finite residue types, whose 128 chord choices have all been proved. -/
theorem terminal_affine_h_frame [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : Fin 5 ↪ V) (hf : HFrame G f) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have main : ∀ n : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (g : Fin 5 ↪ W), Fintype.card W=n → HFrame H g →
      ∃ P : Cycle13.CyclePacking H,
        P.cost ≤ 19*(Fintype.card W-1)+6*H.edgeSet.ncard := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H g hcard hg
      by_cases htwin : ∃ k : Fin 5, (k=2 ∨ k=3) ∧ ∃ x y,
          x≠y ∧ HSpoke H g k x ∧ HSpoke H g k y
      · obtain ⟨k,hk,x,y,hxy,hx,hy⟩ := htwin
        let S : Finset W := ({x,y}:Finset W)ᶜ
        have hS : ∀ i, g i∈S := by
          intro i
          simp only [S,mem_compl,mem_insert,mem_singleton,not_or]
          exact ⟨(hx.1 i).symm,(hy.1 i).symm⟩
        let g' : Fin 5 ↪ (S:Set W) := ⟨fun i => ⟨g i,hS i⟩,by
          intro i j he; exact g.injective (congrArg Subtype.val he)⟩
        have hg' : HFrame (H.induce (S:Set W)) g' := h_frame_induce g hg (S:Set W) hS
        have hc : Fintype.card (S:Set W)=S.card := Fintype.card_of_finset' _ (by simp)
        have hsmaller : Fintype.card (S:Set W)<n := by
          have hh := Finset.card_add_card_compl ({x,y}:Finset W)
          rw [Finset.card_pair hxy] at hh
          rw [hc]
          dsimp only [S]
          omega
        obtain ⟨P,hP⟩ := ih _ hsmaller (S:Set W) (H.induce (S:Set W)) g' rfl hg'
        rw [hc] at hP
        have h0k : (0:Fin 5)≠k := by rcases hk with rfl | rfl <;> decide
        exact terminal_delete_degree_two_twins H (g 0) (g k) x y
          (g.injective.ne h0k) hxy (hx.1 0).symm (hy.1 0).symm
          (hx.1 k).symm (hy.1 k).symm hx.2 hy.2 P hP
      · apply terminal_h_without_twins H g hg
        intro k hk x y hx hy
        by_contra hxy
        exact htwin ⟨k,hk,x,y,hxy,hx,hy⟩
  exact main _ V G f rfl hf

end
end Cycle12
