import Cycle12.Foundations.AnchorParameters

namespace Cycle13
open Finset SimpleGraph Real
open GlobalCutParameters (side smallSide residualGraph dependencyDegree)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem anchor_cut_implies_oriented_tail (G : SimpleGraph V) (U X C S T : Finset V) (k : ℕ)
    {L err τ ρ : ℝ} (hbad : BadAnchorCut G U X C L)
    (herr : sampledErrorWeight G U C (U∩S) ≤ err*L*X.card)
    (hthreshold : (1+err)*L*X.card ≤ τ*(Fintype.card
      ((truncatedCut G (smallerCutSide S) k).induce (↑(univ\T):Set V)).edgeSet:ℝ)*ρ^2) :
    (sampledEdgeCount ((truncatedCut G (smallerCutSide S) k).induce (↑(univ\T):Set V))
      {v | v.val∈U}:ℝ) ≤ τ*(Fintype.card
        ((truncatedCut G (smallerCutSide S) k).induce (↑(univ\T):Set V)).edgeSet:ℝ)*ρ^2 := by
  have hc := weighted_cut_perturbation G U C (U∩S) hbad.2.1 inter_subset_left
  have he : U\(U∩S)=U\S := by ext v; simp
  rw [he] at hc
  have ht := sampled_truncated_cut_le G (smallerCutSide S) U (univ\T) k
  rw [smallerCutSide_sample_cut] at ht
  have htR := Nat.cast_le (α:=ℝ).mpr ht
  have hcost := hbad.2.2.2.2
  have hnon : (0:ℝ) ≤ (G.interedges X (U\C)).card := Nat.cast_nonneg _
  nlinarith

namespace AnchorParameters

theorem witness_implies_tail (K : AnchorParameters) {p q ρ : unitInterval}
    (hK : K.Valid p q ρ (Fintype.card V)) (G : SimpleGraph V) (hG : GlobalCutProfile G K.h)
    (U T : Finset V) (ξ : V→Option V)
    (hw : AnchorCopyWitness G K.δ K.β K.L K.lower K.upper K.err K.miss K.cap U T ξ) :
    K.upperEvent p U T ξ ∨ K.jansonEvent G ρ U T ξ := by
  by_cases hup : K.upperEvent p U T ξ
  · exact Or.inl hup
  apply Or.inr
  obtain ⟨hcond,X,C,hbad,herr,hmiss,hT⟩ := hw
  let label : {A : Finset V // A⊆T} := ⟨C∩T,inter_subset_right⟩
  let S := side T ξ label
  let B := smallSide T ξ label
  have hupB : ((U\S).card:ℝ) ≤ K.slope*(p:ℝ)*Sᶜ.card+K.b := by
    by_contra! hn
    exact hup ⟨label,Or.inr hn⟩
  have hpop : K.c*X.card ≤ (B.card:ℝ) :=
    anchor_classified_population G U X C S hbad.1 hbad.2.1 hbad.2.2.1
      hK.degree_pos hK.error_pos.le hK.anchor_pos.le (mul_pos hK.slope_pos hK.p_pos)
      hK.population_pos.le hK.population_first hK.population_second
      (fun v _ => hcond.2.2.1 v) herr hmiss hcond.1 hK.population_bound hupB
  have hx := (bad_anchor_cut_sizes G U X C hK.expansion_pos hK.anchor_pos
    (fun v _ => hcond.2.2.1 v) hcond.2.2.2 hbad).2.2
  have hel : K.eligible T ξ label :=
    hK.side_scale_bound.trans ((mul_le_mul_of_nonneg_left hx hK.population_pos.le).trans hpop)
  have hm := K.retained_edges hK G hG T ξ label hT hel
  have hthreshold : (1+K.err)*K.L*X.card ≤
      K.τ*(Fintype.card (residualGraph G T ξ label).edgeSet:ℝ)*(ρ:ℝ)^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hK.cut_threshold (Nat.cast_nonneg (α:=ℝ) X.card)
    have h₂ := mul_le_mul_of_nonneg_left hpop
      (show 0 ≤ K.τ*K.κ*K.h*(ρ:ℝ)^2 by
        exact mul_nonneg (mul_nonneg (mul_nonneg hK.fraction_nonneg hK.retained_nonneg)
          hK.scale_pos.le) (sq_nonneg _))
    have h₃ := mul_le_mul_of_nonneg_left hm (mul_nonneg hK.fraction_nonneg (sq_nonneg (ρ:ℝ)))
    change K.κ*K.h*B.card ≤ _ at hm
    change (K.τ*(ρ:ℝ)^2)*(K.κ*K.h*B.card) ≤ _ at h₃
    nlinarith
  exact ⟨hT,label,hel,anchor_cut_implies_oriented_tail G U X C S T B.card hbad herr hthreshold⟩

end AnchorParameters
end
end Cycle13
