import Cycle12.Foundations.GraphBranchCut

/-! Deterministic geometry of an approximating sampled cut. The error
is charged by actual sampled degrees, rather than the ambient order. -/
namespace Cycle13
open Finset SimpleGraph
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def sampledErrorWeight (G : SimpleGraph V) (U A B : Finset V) : ℝ :=
  ∑ v∈A ∆ B, ((neighborsIn G v U).card:ℝ)

theorem weighted_cut_perturbation (G : SimpleGraph V) (U A B : Finset V)
    (hAU : A⊆U) (hBU : B⊆U) :
    ((G.interedges B (U\B)).card:ℝ) ≤ ((G.interedges A (U\A)).card:ℝ)+
      sampledErrorWeight G U A B := by
  let f := fun e : V×V => s(e.1,e.2)
  let E := (G.interedges A (U\A)).image f
  let D := (G.interedges (A ∆ B) U).image f
  have hinj := interedges_sym2_injective G B (U\B)
    (Finset.disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp hy).2 hx))
  have hsub : (G.interedges B (U\B)).image f ⊆ E∪D := by
    intro e he
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := mem_image.mp he
    rcases G.mem_interedges_iff.mp hxy with ⟨hxB,hyUB,hxy⟩
    obtain ⟨hyU,hyB⟩ := mem_sdiff.mp hyUB
    by_cases hxA : x∈A
    · by_cases hyA : y∈A
      · apply mem_union_right; apply mem_image.mpr
        exact ⟨(y,x),G.mem_interedges_iff.mpr
          ⟨mem_symmDiff.mpr (Or.inl ⟨hyA,hyB⟩),hBU hxB,G.adj_symm hxy⟩,Sym2.eq_swap⟩
      · apply mem_union_left; apply mem_image.mpr
        exact ⟨(x,y),G.mem_interedges_iff.mpr ⟨hxA,mem_sdiff.mpr ⟨hyU,hyA⟩,hxy⟩,rfl⟩
    · apply mem_union_right; apply mem_image.mpr
      exact ⟨(x,y),G.mem_interedges_iff.mpr
        ⟨mem_symmDiff.mpr (Or.inr ⟨hxB,hxA⟩),hyU,hxy⟩,rfl⟩
  have hc : (G.interedges B (U\B)).card ≤ (G.interedges A (U\A)).card+
      (G.interedges (A ∆ B) U).card := calc
    _ = ((G.interedges B (U\B)).image f).card := (card_image_of_injOn hinj).symm
    _ ≤ (E∪D).card := card_le_card hsub
    _ ≤ E.card+D.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add card_image_le card_image_le
  have hr : ((G.interedges B (U\B)).card:ℝ) ≤ ((G.interedges A (U\A)).card:ℝ)+
      ((G.interedges (A ∆ B) U).card:ℝ) := by exact_mod_cast hc
  simpa only [sampledErrorWeight,card_interedges_eq_sum_neighborsIn,Nat.cast_sum] using hr

theorem sampled_error_card_bound (G : SimpleGraph V) (U A B : Finset V)
    (hAU : A⊆U) (hBU : B⊆U) {δ : ℝ}
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ)) :
    δ*(A ∆ B).card ≤ sampledErrorWeight G U A B := by
  calc
    _ = ∑ _v∈A ∆ B, δ := by simp [mul_comm]
    _ ≤ _ := sum_le_sum (fun v hv => hdeg v (by
      rcases mem_symmDiff.mp hv with h | h
      · exact hAU h.1
      · exact hBU h.1))

theorem bad_sampled_cut_large (G : SimpleGraph V) (U A : Finset V)
    (hAU : A⊆U) (ha : 0 < (A.card:ℝ)) {δ β : ℝ}
    (hdeg : ∀ v∈A, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ((G.interedges A (U\A)).card:ℝ) < β*A.card) :
    δ-β < (A.card:ℝ) := by
  have hlo : (δ-(A.card:ℝ))*A.card ≤ ((G.interedges A (U\A)).card:ℝ) := by
    apply cut_card_lower_of_neighbors G A (U\A) A (Subset.refl _) (δ-A.card)
    intro v hv
    have hp := neighborsIn_partition_card G v A U hAU
    have hpR : ((neighborsIn G v U).card:ℝ)=((neighborsIn G v A).card:ℝ)+
        ((neighborsIn G v (U\A)).card:ℝ) := by exact_mod_cast hp
    have hc : ((neighborsIn G v A).card:ℝ) ≤ A.card := by
      exact_mod_cast card_le_card (filter_subset (G.Adj v) A)
    have hd := hdeg v hv
    linarith
  have hh : δ-(A.card:ℝ) < β := (mul_lt_mul_iff_left₀ ha).mp (hlo.trans_lt hbad)
  linarith

theorem classified_side_sample_size (G : SimpleGraph V) (U A S : Finset V)
    (hAU : A⊆U) {δ ε : ℝ} (hδ : 0 < δ)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (herr : sampledErrorWeight G U A (U∩S) ≤ δ*ε*A.card) :
    ((U∩S).card:ℝ) ≤ (1+ε)*A.card := by
  have he := sampled_error_card_bound G U A (U∩S) hAU inter_subset_left hdeg
  have hdist : ((A ∆ (U∩S)).card:ℝ) ≤ ε*A.card := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    nlinarith
  have hc := card_le_add_symmDiff (U∩S) A
  rw [symmDiff_comm (U∩S) A] at hc
  have hcR : ((U∩S).card:ℝ) ≤ A.card+(A ∆ (U∩S)).card := by exact_mod_cast hc
  nlinarith

theorem small_sample_cut_localizes (G : SimpleGraph V) (U A S : Finset V)
    (hAU : A⊆U) {δ ε η upper size threshold : ℝ} (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (herr : sampledErrorWeight G U A (U∩S) ≤ δ*ε*A.card)
    (hsmall : (A.card:ℝ) ≤ η*U.card) (hupper : (U.card:ℝ) ≤ upper)
    (hgap : (1+ε)*η*upper < threshold)
    (hreverse : size ≤ (S.card:ℝ) → threshold ≤ ((U∩S).card:ℝ)) :
    (S.card:ℝ) < size := by
  have hc := classified_side_sample_size G U A S hAU hδ hdeg herr
  have hbound : ((U∩S).card:ℝ) < threshold := calc
    _ ≤ (1+ε)*A.card := hc
    _ ≤ (1+ε)*(η*U.card) := mul_le_mul_of_nonneg_left hsmall (by linarith)
    _ ≤ (1+ε)*(η*upper) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hupper hη) (by linarith)
    _ < threshold := by nlinarith [hgap]
  by_contra! hs
  exact (not_le_of_gt hbound) (hreverse hs)

end
end Cycle13
