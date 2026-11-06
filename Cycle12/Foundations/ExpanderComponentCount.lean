import Cycle12.Foundations.GeneralBoundedParity
import Cycle12.Foundations.ExpanderDiameter
import Cycle12.Foundations.ExpansionWithinTools

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem induce_preconnected_congr (G : SimpleGraph V) {S T : Set V} (hST : S=T) :
    (G.induce S).Preconnected ↔ (G.induce T).Preconnected := by
  subst T
  rfl

theorem expansionWithin_univ {G : SimpleGraph V} {h : ℝ}
    (hexp : OAI.ErdosGallai.CutExpansion G h) : ExpansionWithin G univ h := by
  intro U hU hsmall
  simpa only [Finset.card_univ,← Finset.compl_eq_univ_sdiff,cutSize_eq_interedges] using
    cutExpansion_small G hexp (by simpa only [Finset.card_univ] using hsmall)

theorem expander_small_deletion_preconnected (G : SimpleGraph V) {h : ℝ}
    (hexp : OAI.ErdosGallai.CutExpansion G h) (S : Finset V) (hS : (S.card:ℝ) < h) :
    (G.induce ((S:Set V)ᶜ)).Preconnected := by
  have hx := ((expansionWithin_univ hexp).delete_vertices S).induce
  have he : ((univ\S:Finset V):Set V)=(S:Set V)ᶜ := by ext x; simp
  suffices hp : (G.induce ((univ\S:Finset V):Set V)).Preconnected by
    exact (induce_preconnected_congr G he).mp hp
  intro x y
  letI : Nonempty ((univ\S:Finset V):Set V) := ⟨x⟩
  exact (connected_of_cutExpansion _ (sub_pos.mpr hS) hx).preconnected x y

/-- Expansion gives precisely the component bound needed for the parity
blowup. Small deletion sets leave a connected graph; large sets pay by order. -/
theorem expander_deleted_components_bound (G : SimpleGraph V) {h : ℝ} {q : ℕ}
    (hh : 0 < h) (hexp : OAI.ErdosGallai.CutExpansion G h) (hq : 1 ≤ q)
    (hsize : (Fintype.card V:ℝ) ≤ q*h) (S : Set V) (hS : S.Nonempty) :
    Nat.card (G.induce Sᶜ).ConnectedComponent ≤ q*S.ncard := by
  by_cases hs : (S.ncard:ℝ) < h
  · have hp' := expander_small_deletion_preconnected G hexp S.toFinset
      (by simpa only [Set.ncard_eq_toFinset_card'] using hs)
    have hp : (G.induce Sᶜ).Preconnected :=
      (induce_preconnected_congr G (by ext x; simp)).mp hp'
    letI := hp.subsingleton_connectedComponent
    have hc : Nat.card (G.induce Sᶜ).ConnectedComponent ≤ 1 := by
      simpa using Nat.card_le_card_of_injective
        (fun _ : (G.induce Sᶜ).ConnectedComponent => ())
        (fun _ _ _ => Subsingleton.elim _ _)
    have hn : 1 ≤ S.ncard := by
      have hn := Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hS.choose_spec)
      simpa using hn
    exact hc.trans (by nlinarith)
  · have hs' : h ≤ (S.ncard:ℝ) := le_of_not_gt hs
    have hc : Nat.card (G.induce Sᶜ).ConnectedComponent ≤ Fintype.card V := by
      have h₁ := componentCount_le_card (G.induce Sᶜ)
      have h₂ := Fintype.card_le_of_injective (Subtype.val : (Sᶜ:Set V) → V) Subtype.val_injective
      exact h₁.trans h₂
    have hn : (Fintype.card V:ℝ) ≤ (q:ℝ)*S.ncard :=
      hsize.trans (mul_le_mul_of_nonneg_left hs' (Nat.cast_nonneg _))
    exact hc.trans (by exact_mod_cast hn)

end
end Cycle13
