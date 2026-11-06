import Cycle12.Foundations.SamplingGeometry

namespace Cycle12
open SimpleGraph Finset Cycle13
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Only neighbors on the original same side can create a new cut edge
when a vertex is misclassified. -/
def jointCutError (G : SimpleGraph V) (U A B : Finset V) : ℝ :=
  ∑ v∈A ∆ B, ((neighborsIn G v (if v∈A then A else U\A)).card:ℝ)

theorem joint_cut_error_nonneg (G : SimpleGraph V) (U A B : Finset V) :
    0 ≤ jointCutError G U A B := sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- The actual cut perturbation is bounded by same-side error degrees,
retaining the relation between vertex errors and cut-edge errors. -/
theorem joint_cut_perturbation (G : SimpleGraph V) (U A B : Finset V)
    (hAU : A⊆U) (hBU : B⊆U) :
    ((G.interedges B (U\B)).card:ℝ) ≤ ((G.interedges A (U\A)).card:ℝ)+
      jointCutError G U A B := by
  let f := fun e : V×V => s(e.1,e.2)
  let E := (G.interedges A (U\A)).image f
  let D := (A ∆ B).biUnion fun v =>
    (neighborsIn G v (if v∈A then A else U\A)).image (fun w => s(v,w))
  have hsub : (G.interedges B (U\B)).image f ⊆ E∪D := by
    intro e he
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp he
    obtain ⟨hxB,hyUB,hxy⟩ := G.mem_interedges_iff.mp hxy
    obtain ⟨hyU,hyB⟩ := mem_sdiff.mp hyUB
    by_cases hxA : x∈A
    · by_cases hyA : y∈A
      · apply mem_union_right
        apply mem_biUnion.mpr
        refine ⟨y,mem_symmDiff.mpr (Or.inl ⟨hyA,hyB⟩),mem_image.mpr ⟨x,?_,Sym2.eq_swap⟩⟩
        simp only [if_pos hyA,neighborsIn,mem_filter]
        exact ⟨hxA,hxy.symm⟩
      · apply mem_union_left
        exact mem_image.mpr ⟨(x,y),G.mem_interedges_iff.mpr
          ⟨hxA,mem_sdiff.mpr ⟨hyU,hyA⟩,hxy⟩,rfl⟩
    · by_cases hyA : y∈A
      · apply mem_union_left
        exact mem_image.mpr ⟨(y,x),G.mem_interedges_iff.mpr
          ⟨hyA,mem_sdiff.mpr ⟨hBU hxB,hxA⟩,hxy.symm⟩,Sym2.eq_swap⟩
      · apply mem_union_right
        apply mem_biUnion.mpr
        refine ⟨x,mem_symmDiff.mpr (Or.inr ⟨hxB,hxA⟩),mem_image.mpr ⟨y,?_,rfl⟩⟩
        simp only [if_neg hxA,neighborsIn,mem_filter,mem_sdiff]
        exact ⟨⟨hyU,hyA⟩,hxy⟩
  have hinj := interedges_sym2_injective G B (U\B)
    (Finset.disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp hy).2 hx))
  have hD : D.card ≤ ∑ v∈A ∆ B, (neighborsIn G v (if v∈A then A else U\A)).card :=
    card_biUnion_le.trans (sum_le_sum (fun _ _ => card_image_le))
  have hc : (G.interedges B (U\B)).card ≤ (G.interedges A (U\A)).card+
      ∑ v∈A ∆ B, (neighborsIn G v (if v∈A then A else U\A)).card := calc
    _ = ((G.interedges B (U\B)).image f).card := (card_image_of_injOn hinj).symm
    _ ≤ (E∪D).card := card_le_card hsub
    _ ≤ E.card+D.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add card_image_le hD
  unfold jointCutError
  exact_mod_cast hc

/-- A single joint-error budget preserves a small cut and gives two
nonempty classified sides, with no independence or stability assumption. -/
theorem joint_cut_witness (G : SimpleGraph V) (U A B : Finset V)
    (hAU : A⊆U) (hBU : B⊆U) (hA : A.Nonempty) (hsmall : 2*A.card ≤ U.card)
    {z beta tau : ℝ} (hz : 0<z) (hbeta : 0<beta) (hbt : beta<tau)
    (hbad : ((G.interedges A (U\A)).card:ℝ)<beta*z*A.card)
    (hbudget : jointCutError G U A B+tau*z*(A ∆ B).card ≤ (tau-beta)*z*A.card) :
    (A ∆ B).card<A.card ∧ B.Nonempty ∧ (U\B).Nonempty ∧
      ((G.interedges B (U\B)).card:ℝ)<tau*z*min (B.card:ℝ) (U\B).card := by
  have hapos : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have htz := mul_pos (hbeta.trans hbt) hz
  have hZ := joint_cut_error_nonneg G U A B
  have herr : ((A ∆ B).card:ℝ)<A.card := by
    apply (mul_lt_mul_iff_right₀ htz).mp
    have hh := mul_pos (mul_pos hbeta hz) hapos
    nlinarith only [hbudget,hZ,hh]
  have hcard1 : (A.card:ℝ) ≤ B.card+(A ∆ B).card := by
    exact_mod_cast card_le_add_symmDiff A B
  have hcard2 : (B.card:ℝ) ≤ A.card+(A ∆ B).card := by
    simpa only [symmDiff_comm B A] using
      (show (B.card:ℝ) ≤ A.card+(B ∆ A).card by exact_mod_cast card_le_add_symmDiff B A)
  have hcomp : ((U\B).card:ℝ)=(U.card:ℝ)-B.card := by
    rw [card_sdiff_of_subset hBU,Nat.cast_sub (card_le_card hBU)]
  have hsmallR : 2*(A.card:ℝ) ≤ U.card := by exact_mod_cast hsmall
  have hlow : (A.card:ℝ)-(A ∆ B).card ≤ min (B.card:ℝ) (U\B).card := by
    apply le_min
    · linarith only [hcard1]
    · rw [hcomp]
      linarith only [hcard2,hsmallR]
  have hbpos : (0:ℝ)<B.card := by linarith only [hcard1,herr]
  have hcpos : (0:ℝ)<(U\B).card := by
    have hh := hlow.trans (min_le_right _ _)
    linarith only [hh,herr]
  refine ⟨by exact_mod_cast herr,card_pos.mp (by exact_mod_cast hbpos),
    card_pos.mp (by exact_mod_cast hcpos),?_⟩
  have hc := joint_cut_perturbation G U A B hAU hBU
  have hscale := mul_le_mul_of_nonneg_left hlow htz.le
  nlinarith only [hc,hbad,hbudget,hscale]

end
end Cycle12
