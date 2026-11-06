import Cycle12.Foundations.GlobalCutParameters
import Cycle12.Foundations.CutWitnessFamily

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace GlobalCutParameters

theorem witness_implies_tail (C : GlobalCutParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ (Fintype.card V)) (G : SimpleGraph V) (hG : GlobalCutProfile G C.h)
    (U T : Finset V) (ξ : V→Option V)
    (hw : CutWitnessWithin G C.δ C.β C.err C.upper C.cap (fun _ _ => True) U T ξ) :
    C.upperEvent p U T ξ ∨ C.jansonEvent G ρ U T ξ := by
  by_cases hup : C.upperEvent p U T ξ
  · exact Or.inl hup
  apply Or.inr
  obtain ⟨hupper,hdeg,A,hA,_,herr,hT⟩ := hw
  let label : {A : Finset V // A⊆T} := ⟨A∩T,inter_subset_right⟩
  let S := side T ξ label
  let B := smallSide T ξ label
  have herror : sampledErrorWeight G U A (U∩S) ≤ C.δ*(C.err/C.δ)*A.card := by
    have he : C.δ*(C.err/C.δ)=C.err := by field_simp [hC.degree_pos.ne']
    rw [he]
    exact herr
  have hamin : 0 < C.δ-C.β := sub_pos.mpr hC.cut_lt_degree
  have hsizeA : C.δ-C.β ≤ (A.card:ℝ) :=
    bad_sampled_cut_size_le G U A hA.1 hA.2.1 (fun v hv => hdeg v (hA.1 hv)) hA.2.2.2
  have hup₁ : ((U∩S).card:ℝ) ≤ C.slope*(p:ℝ)*S.card+C.b := by
    by_contra! hn
    exact hup ⟨label,Or.inl hn⟩
  have hup₂ : ((U\S).card:ℝ) ≤ C.slope*(p:ℝ)*Sᶜ.card+C.b := by
    by_contra! hn
    exact hup ⟨label,Or.inr hn⟩
  have hboth := classified_both_sides_population G U A S hA.1 hA.2.2.1
    hC.degree_pos hamin hsizeA hdeg herror (mul_pos hC.slope_pos hC.p_pos)
    hC.intercept_nonneg hC.population_bound hup₁ hup₂
  have hpop : C.c*A.card ≤ (B.card:ℝ) := smallerCutSide_population S hboth.1 hboth.2
  have hel : C.eligible T ξ label :=
    hC.side_scale_bound.trans ((mul_le_mul_of_nonneg_left hsizeA hC.population_pos.le).trans hpop)
  have hm := C.retained_edges hC G hG T ξ label hT hel
  have hthreshold : (C.β+C.err)*A.card ≤
      C.τ*(Fintype.card (residualGraph G T ξ label).edgeSet:ℝ)*(ρ:ℝ)^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hC.cut_threshold (Nat.cast_nonneg (α:=ℝ) A.card)
    have h₂ := mul_le_mul_of_nonneg_left hpop
      (show 0 ≤ C.τ*C.κ*C.h*(ρ:ℝ)^2 by
        exact mul_nonneg (mul_nonneg (mul_nonneg hC.fraction_nonneg hC.retained_nonneg)
          hC.scale_pos.le) (sq_nonneg _))
    have h₃ := mul_le_mul_of_nonneg_left hm (mul_nonneg hC.fraction_nonneg (sq_nonneg (ρ:ℝ)))
    change C.κ*C.h*B.card ≤ _ at hm
    change (C.τ*(ρ:ℝ)^2)*(C.κ*C.h*B.card) ≤ _ at h₃
    nlinarith
  refine ⟨hT,label,hel,?_⟩
  exact small_cut_implies_oriented_tail G U A S T B.card hA.1 hA.2.2.2 herr hthreshold

end GlobalCutParameters
end
end Cycle13
