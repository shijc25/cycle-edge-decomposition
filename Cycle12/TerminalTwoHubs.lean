import Cycle12.TwinReduction
import Cycle12.TerminalSmallBase

/-! An infinite family from the short-circumference classification is proved
without a bounded-order test: arbitrary K₂,t, with an optional hub edge. -/
namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem terminal_affine_two_hubs {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b : V) (hab : a ≠ b)
    (hshape : ∀ x, x ≠ a → x ≠ b → ∀ v, G.Adj x v ↔ v=a ∨ v=b) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have main : ∀ n : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (a b : W), Fintype.card W=n → a ≠ b →
      (∀ x, x ≠ a → x ≠ b → ∀ v, H.Adj x v ↔ v=a ∨ v=b) →
      ∃ P : Cycle13.CyclePacking H,
        P.cost ≤ 19*(Fintype.card W-1)+6*H.edgeSet.ncard := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H a b hcard hab hshape
      letI : Nonempty W := ⟨a⟩
      by_cases hsmall : Fintype.card W ≤ 3
      · exact terminal_affine_card_le_three H hsmall
      have htwo : 1 < (({a,b}:Finset W)ᶜ).card := by
        have hh := Finset.card_add_card_compl ({a,b}:Finset W)
        rw [Finset.card_pair hab] at hh
        omega
      obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp htwo
      have hx' : x ≠ a ∧ x ≠ b := by simpa only [mem_compl,mem_insert,mem_singleton,not_or] using hx
      have hy' : y ≠ a ∧ y ≠ b := by simpa only [mem_compl,mem_insert,mem_singleton,not_or] using hy
      let S : Finset W := ({x,y}:Finset W)ᶜ
      have ha : a ∈ S := by simp [S,hx'.1.symm,hy'.1.symm]
      have hb : b ∈ S := by simp [S,hx'.2.symm,hy'.2.symm]
      let a' : (S:Set W) := ⟨a,ha⟩
      let b' : (S:Set W) := ⟨b,hb⟩
      have hab' : a' ≠ b' := fun he => hab (congrArg Subtype.val he)
      have hshape' : ∀ z : (S:Set W), z ≠ a' → z ≠ b' → ∀ v,
          (H.induce (S:Set W)).Adj z v ↔ v=a' ∨ v=b' := by
        intro z hza hzb v
        have hz₁ : z.val ≠ a := fun he => hza (Subtype.ext he)
        have hz₂ : z.val ≠ b := fun he => hzb (Subtype.ext he)
        simpa only [SimpleGraph.induce_adj,Subtype.ext_iff,a',b'] using hshape z.val hz₁ hz₂ v.val
      have horder : Fintype.card (S:Set W) < n := by
        have hc : Fintype.card (S:Set W)=S.card := Fintype.card_of_finset' _ (by simp)
        have hh := Finset.card_add_card_compl ({x,y}:Finset W)
        rw [Finset.card_pair hxy] at hh
        rw [hc]
        dsimp [S]
        omega
      obtain ⟨P,hP⟩ := ih _ horder (S:Set W) (H.induce (S:Set W)) a' b' rfl hab' hshape'
      have hc : Fintype.card (S:Set W)=S.card := Fintype.card_of_finset' _ (by simp)
      rw [hc] at hP
      exact terminal_delete_degree_two_twins H a b x y hab hxy hx'.1.symm hy'.1.symm
        hx'.2.symm hy'.2.symm (hshape x hx'.1 hx'.2) (hshape y hy'.1 hy'.2) P hP
  exact main _ V G a b rfl hab hshape

end
end Cycle12
