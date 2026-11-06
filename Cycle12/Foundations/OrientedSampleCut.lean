import Cycle12.Foundations.SampledCutPopulation

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def smallerCutSide (S : Finset V) : Finset V := if S.card ≤ Sᶜ.card then S else Sᶜ

theorem smallerCutSide_card (S : Finset V) : (smallerCutSide S).card=min S.card Sᶜ.card := by
  unfold smallerCutSide
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem smallerCutSide_small (S : Finset V) : 2*(smallerCutSide S).card ≤ Fintype.card V := by
  rw [smallerCutSide_card]
  have hh := S.card_compl
  have hc := card_le_univ S
  omega

theorem smallerCutSide_population (S : Finset V) {a : ℝ}
    (h₁ : a ≤ (S.card:ℝ)) (h₂ : a ≤ (Sᶜ.card:ℝ)) : a ≤ ((smallerCutSide S).card:ℝ) := by
  unfold smallerCutSide
  split_ifs <;> assumption

theorem sample_cut_compl (G : SimpleGraph V) (U S : Finset V) :
    (G.interedges (U∩Sᶜ) (U\Sᶜ)).card=(G.interedges (U∩S) (U\S)).card := by
  have h₁ : U∩Sᶜ=U\S := by ext v; simp
  have h₂ : U\Sᶜ=U∩S := by ext v; simp
  rw [h₁,h₂]
  letI : Std.Symm G.Adj := ⟨fun _ _ h => G.adj_symm h⟩
  exact Rel.card_interedges_comm (r:=G.Adj) (U\S) (U∩S)

theorem smallerCutSide_sample_cut (G : SimpleGraph V) (U S : Finset V) :
    (G.interedges (U∩smallerCutSide S) (U\smallerCutSide S)).card=
      (G.interedges (U∩S) (U\S)).card := by
  unfold smallerCutSide
  split_ifs
  · rfl
  · exact sample_cut_compl G U S

theorem small_cut_implies_oriented_tail (G : SimpleGraph V) (U A S T : Finset V) (k : ℕ)
    (hAU : A⊆U) {β err τ ρ : ℝ}
    (hbad : ((G.interedges A (U\A)).card:ℝ) ≤ β*A.card)
    (herr : sampledErrorWeight G U A (U∩S) ≤ err*A.card)
    (hthreshold : (β+err)*A.card ≤ τ*(Fintype.card
      ((truncatedCut G (smallerCutSide S) k).induce (↑(univ\T):Set V)).edgeSet:ℝ)*ρ^2) :
    (sampledEdgeCount ((truncatedCut G (smallerCutSide S) k).induce (↑(univ\T):Set V))
      {v | v.val∈U}:ℝ) ≤ τ*(Fintype.card
        ((truncatedCut G (smallerCutSide S) k).induce (↑(univ\T):Set V)).edgeSet:ℝ)*ρ^2 := by
  have hc := weighted_cut_perturbation G U A (U∩S) hAU inter_subset_left
  have he : U\(U∩S)=U\S := by ext v; simp
  rw [he] at hc
  have ht := sampled_truncated_cut_le G (smallerCutSide S) U (univ\T) k
  rw [smallerCutSide_sample_cut] at ht
  have htR := Nat.cast_le (α:=ℝ).mpr ht
  linarith

end
end Cycle13
