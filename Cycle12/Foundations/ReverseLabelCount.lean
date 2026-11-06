import Cycle12.Foundations.MarkedLabelOriginal
import Cycle12.Foundations.SubsetChernoff

/-! Reverse label counting: a side of large original order cannot have
too few sampled vertices, uniformly over all marked labels. The
auxiliary random choice is averaged before the residual sample. -/
namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem label_card (T : Finset V) : Fintype.card {A : Finset V // A⊆T}=2^T.card := by
  rw [Fintype.card_subtype]
  have he : univ.filter (fun A : Finset V => A⊆T)=T.powerset := by ext A; simp
  rw [he,card_powerset]

theorem marked_side_lower_count (ρ : unitInterval) (T C : Finset V) {ℓ : ℝ}
    (hmean : ℓ ≤ (ρ:ℝ)*(C\T).card) :
    (subsetBernoulli (univ\T) ρ).prob (fun S => (((T∪S)∩C).card:ℝ) < ℓ/2) ≤
      exp (-ℓ/8) := by
  have hh := subsetBernoulli_lower_half (univ\T) ρ (C\T)
    (sdiff_subset_sdiff_left T (subset_univ C))
  have hevent : ∀ S : Finset V, (((T∪S)∩C).card:ℝ) < ℓ/2 →
      ((S∩(C\T)).card:ℝ) ≤ (ρ:ℝ)*(C\T).card/2 := by
    intro S hS
    have hc := marked_sample_inter_card T S C
    have hcR : (((T∪S)∩C).card:ℝ)=((T∩C).card:ℝ)+(S∩(C\T)).card := by exact_mod_cast hc
    have hn : (0:ℝ) ≤ (T∩C).card := Nat.cast_nonneg _
    linarith
  apply ((FiniteLaw.prob_mono _ hevent).trans hh).trans
  apply exp_le_exp.mpr
  linarith

theorem marked_all_labels_lower_count (ρ : unitInterval) (T : Finset V)
    (side : {A : Finset V // A⊆T} → Finset V) {size cap ℓ : ℝ}
    (hT : (T.card:ℝ) ≤ cap) (hmean : ℓ ≤ (ρ:ℝ)*(size-cap)) :
    (subsetBernoulli (univ\T) ρ).prob
      (fun S => ∃ A, size ≤ ((side A).card:ℝ) ∧ (((T∪S)∩side A).card:ℝ) < ℓ/2) ≤
        (2:ℝ)^T.card*exp (-ℓ/8) := by
  have hh := (subsetBernoulli (univ\T) ρ).prob_exists_le_sum
    (fun A S => size ≤ ((side A).card:ℝ) ∧ (((T∪S)∩side A).card:ℝ) < ℓ/2)
  apply hh.trans
  have hpoint : ∀ A : {A : Finset V // A⊆T},
      (subsetBernoulli (univ\T) ρ).prob
        (fun S => size ≤ ((side A).card:ℝ) ∧ (((T∪S)∩side A).card:ℝ) < ℓ/2) ≤ exp (-ℓ/8) := by
    intro A
    by_cases hs : size ≤ ((side A).card:ℝ)
    · apply (FiniteLaw.prob_mono _ (fun S h => h.2)).trans
      apply marked_side_lower_count
      have hc := card_sdiff_add_card_inter (side A) T
      have hi := card_le_card (inter_subset_right (s₁:=side A) (s₂:=T))
      have hcR : (((side A)\T).card:ℝ)+(((side A)∩T).card:ℝ)=(side A).card := by exact_mod_cast hc
      have hiR : (((side A)∩T).card:ℝ) ≤ T.card := by exact_mod_cast hi
      have hb : size-cap ≤ (((side A)\T).card:ℝ) := by linarith
      exact hmean.trans (mul_le_mul_of_nonneg_left hb ρ.2.1)
    · simp only [hs,false_and,FiniteLaw.prob,if_false,FiniteLaw.expect_const]
      exact (exp_pos _).le
  have hsum := sum_le_sum (s:=univ) (fun A _ => hpoint A)
  simpa only [sum_const,card_univ,label_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hsum

theorem reverse_label_count_bound (markP ρ : unitInterval)
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V → FiniteLaw Ξ)
    (side : ∀ T : Finset V, Ξ → {A : Finset V // A⊆T} → Finset V)
    {size cap ℓ : ℝ} (hmean : ℓ ≤ (ρ:ℝ)*(size-cap)) :
    (bernoulliSubset markP).expect (fun T => (κ T).expect (fun ξ =>
      (subsetBernoulli (univ\T) ρ).prob (fun S => (T.card:ℝ) ≤ cap ∧
        ∃ A, size ≤ ((side T ξ A).card:ℝ) ∧ (((T∪S)∩side T ξ A).card:ℝ) < ℓ/2))) ≤
      exp (-ℓ/8+(markP:ℝ)*Fintype.card V) := by
  have hpoint : ∀ T, (κ T).expect (fun ξ =>
      (subsetBernoulli (univ\T) ρ).prob (fun S => (T.card:ℝ) ≤ cap ∧
        ∃ A, size ≤ ((side T ξ A).card:ℝ) ∧ (((T∪S)∩side T ξ A).card:ℝ) < ℓ/2)) ≤
      (2:ℝ)^T.card*exp (-ℓ/8) := by
    intro T
    apply le_trans ((κ T).expect_mono (Y:=fun _ => (2:ℝ)^T.card*exp (-ℓ/8)) ?_)
      (le_of_eq ((κ T).expect_const _))
    intro ξ
    by_cases hT : (T.card:ℝ) ≤ cap
    · exact (FiniteLaw.prob_mono _ (fun S h => h.2)).trans
        (marked_all_labels_lower_count ρ T (side T ξ) hT hmean)
    · simp only [hT,false_and,FiniteLaw.prob,if_false,FiniteLaw.expect_const]
      positivity
  apply ((bernoulliSubset markP).expect_mono hpoint).trans
  rw [FiniteLaw.expect_mul_const]
  have hh := bernoulliSubset_generating_le_exp (V:=V) markP (z:=2) (by norm_num)
  norm_num only [show (2:ℝ)-1=1 by norm_num,mul_one] at hh
  apply (mul_le_mul_of_nonneg_right hh (exp_pos _).le).trans_eq
  rw [← exp_add]
  congr 1
  ring

end
end Cycle13
