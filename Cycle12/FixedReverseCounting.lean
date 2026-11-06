import Cycle12.FixedMarkedUnion
import Cycle12.FixedSampleTails
import Cycle12.JansonPhiSeries

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

theorem fixed_count_lower_fraction (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {ell fraction : ℝ}
    (hell : 0 < ell) (hf0 : 0 < fraction) (hf1 : fraction < 1)
    (hmean : ell ≤ ((k:ℝ)/D.card)*B.card) :
    (fixedSizeLaw D k).prob (fun R => ((R∩B).card:ℝ) ≤ fraction*ell) ≤
      exp (-(1-fraction)^2*ell/2) := by
  have hh := fixed_sample_lower_chernoff D B hD hB hk (mu:=1) hell hf0 hf1
    (by simpa only [one_mul] using hmean)
  have hphi := full_janson_phi_series_lower 1 fraction hf0 hf1.le
  norm_num [jansonPhiPolynomial] at hphi
  apply hh.trans
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hphi hell.le
  simp only [one_div,log_inv,fullJansonPhi] at hm ⊢
  nlinarith only [hm]

theorem fixed_marked_side_lower_fraction (T C : Finset V) {k : ℕ}
    (hD : (univ\T).Nonempty) (hk : k ≤ (univ\T).card) {ell fraction : ℝ}
    (hell : 0 < ell) (hf0 : 0 < fraction) (hf1 : fraction < 1)
    (hmean : ell ≤ ((k:ℝ)/(univ\T).card)*(C\T).card) :
    (fixedSizeLaw (univ\T) k).prob (fun R => (((T∪R)∩C).card:ℝ) < fraction*ell) ≤
      exp (-(1-fraction)^2*ell/2) := by
  have hh := fixed_count_lower_fraction (univ\T) (C\T) hD
    (sdiff_subset_sdiff_left T (subset_univ C)) hk hell hf0 hf1 hmean
  apply (le_trans _ hh)
  apply FiniteLaw.prob_mono
  intro R hR
  have hsub : R∩(C\T)⊆(T∪R)∩C := by
    intro v hv
    exact mem_inter.mpr ⟨mem_union_right _ (mem_inter.mp hv).1,(mem_sdiff.mp (mem_inter.mp hv).2).1⟩
  exact ((Nat.cast_le (α:=ℝ)).mpr (card_le_card hsub)).trans hR.le

/-- The reverse-count event localizes all label-dependent sides in the
original fixed-size experiment, at the exact residual sampling mean. -/
theorem fixed_marked_reverse_count_bound {N t : ℕ} (hN : N ≤ Fintype.card V)
    (ht : t ≤ N) (htD : t < Fintype.card V) (kap : Finset V → FiniteLaw Ξ)
    (S : Finset V → Finset V → Ξ → Finset V) {size ell fraction : ℝ}
    (hell : 0 < ell) (hf0 : 0 < fraction) (hf1 : fraction < 1)
    (hmean : ell ≤ (((N-t:ℕ):ℝ)/(Fintype.card V-t:ℕ))*(size-t)) :
    (fixedMarkedExperiment (univ:Finset V) N t kap).prob (fun x => ∃ A⊆x.2.1,
      size ≤ ((S x.2.1 A x.2.2).card:ℝ) ∧ ((x.1∩S x.2.1 A x.2.2).card:ℝ) < fraction*ell) ≤
      (2:ℝ)^t*exp (-(1-fraction)^2*ell/2) := by
  apply fixed_marked_uniform_label_bound (univ:Finset V) (by simpa using hN) ht kap
    (fun U T xi A => size ≤ ((S T A xi).card:ℝ) ∧ ((U∩S T A xi).card:ℝ) < fraction*ell)
  intro T _ hT xi A _
  by_cases hs : size ≤ ((S T A xi).card:ℝ)
  · have hcard : (univ\T).card=Fintype.card V-t := by
      rw [card_sdiff_of_subset (subset_univ T),card_univ,hT]
    have hD : (univ\T).Nonempty := card_pos.mp (by rw [hcard]; omega)
    have hk : N-t ≤ (univ\T).card := by rw [hcard]; omega
    have hp : 0 ≤ ((N-t:ℕ):ℝ)/(univ\T).card := by positivity
    have hsplit : (((S T A xi)\T).card:ℝ)+((S T A xi∩T).card:ℝ)=(S T A xi).card := by
      exact_mod_cast card_sdiff_add_card_inter (S T A xi) T
    have hinter : ((S T A xi∩T).card:ℝ) ≤ (t:ℝ) := by
      rw [← hT]
      exact_mod_cast card_le_card (inter_subset_right (s₁:=S T A xi) (s₂:=T))
    have hsize : size-t ≤ (((S T A xi)\T).card:ℝ) := by linarith only [hs,hsplit,hinter]
    have hm : ell ≤ (((N-t:ℕ):ℝ)/(univ\T).card)*((S T A xi)\T).card := by
      apply (show ell ≤ (((N-t:ℕ):ℝ)/(univ\T).card)*(size-t) by simpa only [hcard] using hmean).trans
      exact mul_le_mul_of_nonneg_left hsize hp
    exact (FiniteLaw.prob_mono _ (fun _ h => h.2)).trans
      (fixed_marked_side_lower_fraction T (S T A xi) hD hk hell hf0 hf1 hm)
  · simp only [hs,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
    exact (exp_pos _).le

end
end Cycle12
