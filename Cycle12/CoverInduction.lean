import Cycle12.CoverGraphGreedy
import Cycle12.CoverIrreducibleCuts

namespace Cycle12
open SimpleGraph Finset Real Cycle13 Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The compositional interface for the one irreducible graph case. The
table theorem supplies this in MixedCover; it is not an axiom. -/
def IrreducibleCoverTheorem : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (0:ℝ) < Fintype.card V → (0:ℝ) < G.edgeSet.ncard →
    coverGraphX (Fintype.card V) G.edgeSet.ncard ≤ (17/250) → CoverSparseCutIrreducible G →
    (∀ v, coverDeleteThreshold (Fintype.card V) G.edgeSet.ncard ≤ (G.degree v:ℝ)) →
    FineCover G 2 ∧ CoarseCover G 1

/-- Strong induction on actual vertex types: trivial, greedy, sparse cut,
low-degree deletion, then the irreducible table case. -/
theorem cover_induction (hHard : IrreducibleCoverTheorem)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    FineCover G 2 ∧ CoarseCover G 1 := by
  have main : ∀ n : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W=n → FineCover H 2 ∧ CoarseCover H 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H hcard
      by_cases htrivial : (H.edgeSet.ncard:ℝ) ≤ coverGraphBudget (Fintype.card W) H.edgeSet.ncard
      · exact ⟨fineCover_trivial H (by norm_num) htrivial,
          coarseCover_trivial H (by norm_num) htrivial⟩
      have hF := lt_of_not_ge htrivial
      obtain ⟨hn,hm,hv,hnlarge,hFB⟩ := cover_nontrivial_graph H hF
      by_cases hgreedy : (17/250) ≤ coverGraphX (Fintype.card W) H.edgeSet.ncard
      · exact cover_greedy H hF hgreedy
      have hx := (lt_of_not_ge hgreedy).le
      by_cases hcut : ∃ S : Finset W, S.Nonempty ∧ 2*(S.card:ℝ) ≤ Fintype.card W ∧
          (cutSize H S:ℝ) ≤ coverCutThreshold (Fintype.card W) H.edgeSet.ncard ((S.card:ℝ)/Fintype.card W)
      · obtain ⟨S,hS,hside,hcut⟩ := hcut
        have hpos : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
        have hSlt : S.card < Fintype.card W := by exact_mod_cast (show (S.card:ℝ) < Fintype.card W by linarith)
        have hc := card_add_card_compl S
        have hSc : (Sᶜ : Finset W).Nonempty := card_pos.mp (by omega)
        have hc₁ : Fintype.card (S:Set W)=S.card := Fintype.card_of_finset' _ (by simp)
        have hc₂ : Fintype.card ((Sᶜ : Finset W):Set W)=(Sᶜ : Finset W).card := Fintype.card_of_finset' _ (by simp)
        have hsmall₁ : Fintype.card (S:Set W) < n := by rw [hc₁,← hcard]; exact hSlt
        have hsmall₂ : Fintype.card ((Sᶜ : Finset W):Set W) < n := by
          rw [hc₂,← hcard]
          have hh := card_pos.mpr hS
          omega
        obtain ⟨h₁a,h₁b⟩ := ih _ hsmall₁ (S:Set W) (H.induce (S:Set W)) rfl
        obtain ⟨h₂a,h₂b⟩ := ih _ hsmall₂ ((Sᶜ : Finset W):Set W)
          (H.induce ((Sᶜ : Finset W):Set W)) rfl
        have hpay := cover_graph_sparse_cut_payment H S
          (by simpa only [Set.fintypeCard_eq_ncard] using hm)
          (by simpa only [Set.fintypeCard_eq_ncard] using hFB)
          (by simpa only [Set.fintypeCard_eq_ncard] using hcut)
        simp only [Set.fintypeCard_eq_ncard] at hpay
        exact ⟨fineCover_cut H S hS hSc h₁a h₂a hpay,
          coarseCover_cut H S h₁b h₂b hpay⟩
      have hI : CoverSparseCutIrreducible H := by
        intro S hS hside
        simpa only [Set.fintypeCard_eq_ncard] using (lt_of_not_ge (fun he => hcut ⟨S,hS,hside,he⟩)).le
      by_cases hdelete : ∃ v : W, (H.degree v:ℝ) ≤ coverDeleteThreshold (Fintype.card W) H.edgeSet.ncard
      · obtain ⟨v,hdegree⟩ := hdelete
        have hc := delete_vertex_order v
        have hsmall : Fintype.card ((({v}:Finset W)ᶜ : Finset W):Set W) < n := by omega
        obtain ⟨h₁,h₂⟩ := ih _ hsmall ((({v}:Finset W)ᶜ : Finset W):Set W)
          (H.induce ((({v}:Finset W)ᶜ : Finset W):Set W)) rfl
        have hdeg : (H.degree v:ℝ) ≤ H.edgeSet.ncard := by
          have hh := H.degree_le_card_edgeFinset v
          rw [H.edgeFinset_card,Set.fintypeCard_eq_ncard] at hh
          exact_mod_cast hh
        have hpay := cover_delete_pays_vertex (by linarith : (100:ℝ) ≤ Fintype.card W)
          hm (Nat.cast_nonneg (α:=ℝ) (H.degree v)) hdeg hFB hdegree
        have hn₁ : 1 < Fintype.card W := by exact_mod_cast (show (1:ℝ) < Fintype.card W by linarith)
        exact ⟨fineCover_delete H v (by norm_num) hn₁ h₁ hpay,
          coarseCover_delete H v (by norm_num) h₂ hpay⟩
      apply hHard W H hn hm hx hI
      intro v
      exact (lt_of_not_ge (fun he => hdelete ⟨v,he⟩)).le
  exact main _ V G rfl

end
end Cycle12
