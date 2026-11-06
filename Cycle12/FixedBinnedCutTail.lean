import Cycle12.CappedLabelEntropy
import Cycle12.FixedCutLabelTail

namespace Cycle12
open Finset Cycle13 SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ I : Type} [Fintype V] [DecidableEq V] [Fintype Ξ] [Fintype I]

/-- A finite family of population ranges. Each range pays its own label
entropy; no independence of the label-dependent residual graphs is assumed. -/
theorem fixed_marked_binned_cut_bound (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (S : Finset V → Finset V → Ξ → Finset V)
    (lambda M fraction : I → Finset V → Finset V → Ξ → ℝ)
    (eligible : I → Finset V → Finset V → Ξ → Prop)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    (rho eta : I → ℝ) (hr : ∀ i, 0 < rho i) (he : ∀ i, 0 ≤ eta i)
    (hvalid : ∀ i T, T.card=t → ∀ A⊆T, ∀ xi, eligible i T A xi →
      RoundedCutLabelValid G (S T A xi) T p (lambda i T A xi) (M i T A xi)
        (fraction i T A xi) (eta i)) :
    (fixedMarkedExperiment (univ:Finset V) N t kap).prob (fun x => ∃ i, ∃ A⊆x.2.1,
      (A.card:ℝ) ≤ rho i*t ∧ eligible i x.2.1 A x.2.2 ∧
        ((G.interedges (x.1∩S x.2.1 A x.2.2) (x.1\S x.2.1 A x.2.2)).card:ℝ) ≤
          fraction i x.2.1 A x.2.2*(M i x.2.1 A x.2.2*(p:ℝ)^2)) ≤
      ∑ i, exp ((t:ℝ)*cappedLabelEntropy (rho i))*eta i := by
  apply (FiniteLaw.prob_exists_le_sum _ _).trans
  apply sum_le_sum
  intro i _
  apply fixed_marked_capped_minority_bound (univ:Finset V) (by simpa using hN) ht kap
    (fun U T xi A => eligible i T A xi ∧
      ((G.interedges (U∩S T A xi) (U\S T A xi)).card:ℝ) ≤
        fraction i T A xi*(M i T A xi*(p:ℝ)^2)) (hr i) (he i)
  intro T _ hT xi A hA _
  by_cases hel : eligible i T A xi
  · have hcard : (univ\T).card=Fintype.card V-t := by
      rw [card_sdiff_of_subset (subset_univ T),card_univ,hT]
    have htail := fixed_remaining_cut_label_tail G (S T A xi) T p (k:=N-t)
      (by rw [hcard]; omega) (by rwa [hcard]) hp hp0 (hvalid i T hT A hA xi hel)
    exact (FiniteLaw.prob_mono _ (fun _ h => h.2)).trans htail
  · simpa only [hel,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using he i

theorem binned_entropy_tail_uniform {t : ℕ} (rho eta : I → ℝ) {bound : ℝ}
    (h : ∀ i, exp ((t:ℝ)*cappedLabelEntropy (rho i))*eta i ≤ bound) :
    (∑ i, exp ((t:ℝ)*cappedLabelEntropy (rho i))*eta i) ≤ Fintype.card I*bound := by
  calc
    _ ≤ ∑ _i : I, bound := sum_le_sum (fun i _ => h i)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

end
end Cycle12
