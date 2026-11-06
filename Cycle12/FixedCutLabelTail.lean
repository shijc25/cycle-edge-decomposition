import Cycle12.FixedMinorityUnion
import Cycle12.RoundedResidualJanson

namespace Cycle12
open Finset Cycle13 SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

/-- Only deterministic graph data and scalar inequalities; there is no
probability conclusion concealed among these certificate fields. -/
def RoundedCutLabelValid (G : SimpleGraph V) (S T : Finset V)
    (p : unitInterval) (lambda M fraction eta : ℝ) : Prop :=
  S.Nonempty ∧ 1 ≤ lambda ∧ 0 < M ∧
  M ≤ (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ) ∧
  0 ≤ fraction ∧ fraction ≤ 1 ∧
  2*exp (-fullJansonPhi fraction*M*(p:ℝ)^2/
    (1+min ((lambda+1)*S.card) (lambda*S.card+1+M/(lambda*S.card))*(p:ℝ))) ≤ eta

theorem fixed_remaining_cut_label_tail (G : SimpleGraph V) (S T : Finset V)
    (p : unitInterval) {k : ℕ} (hk : k ≤ (univ\T).card)
    (hmean : ((univ\T).card:ℝ)*(p:ℝ)=(k:ℝ)) (hp : (p:ℝ) ≤ 1/2) (hp0 : 0 < (p:ℝ))
    {lambda M fraction eta : ℝ} (hvalid : RoundedCutLabelValid G S T p lambda M fraction eta) :
    (fixedSizeLaw (univ\T) k).prob (fun R =>
      ((G.interedges ((T∪R)∩S) ((T∪R)\S)).card:ℝ) ≤ fraction*(M*(p:ℝ)^2)) ≤ eta := by
  obtain ⟨hS,hl,hM,hret,hf0,hf1,hbudget⟩ := hvalid
  have hj := rounded_residual_sharp_janson G S T hS hl p hk hmean hp hp0 hM hret fraction hf0 hf1
  apply (le_trans _ hj).trans hbudget
  apply FiniteLaw.prob_mono
  intro R hR
  have hc := sampled_truncated_residual_cut_le G S T (T∪R) R (roundedCutCap lambda S) subset_union_right
  exact (Nat.cast_le (α:=ℝ)).mpr hc |>.trans hR

theorem fixed_marked_split_cut_bound (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (S : Finset V → Finset V → Ξ → Finset V)
    (lambda M fraction : Finset V → Finset V → Ξ → ℝ)
    (eligible : Finset V → Finset V → Ξ → Prop)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    {rho cutoff etaSmall etaLarge : ℝ} (hr : 0 < rho) (hrhalf : rho ≤ 1/2)
    (heS : 0 ≤ etaSmall) (heL : 0 ≤ etaLarge)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi, eligible T A xi →
      RoundedCutLabelValid G (S T A xi) T p (lambda T A xi) (M T A xi) (fraction T A xi)
        (if ((S T A xi).card:ℝ) ≤ cutoff then etaSmall else etaLarge)) :
    (fixedMarkedExperiment (univ:Finset V) N t kap).prob (fun x => ∃ A⊆x.2.1,
      ((A.card:ℝ) ≤ rho*t ∧ eligible x.2.1 A x.2.2 ∧ ((S x.2.1 A x.2.2).card:ℝ) ≤ cutoff ∧
        ((G.interedges (x.1∩S x.2.1 A x.2.2) (x.1\S x.2.1 A x.2.2)).card:ℝ) ≤
          fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2)) ∨
      (eligible x.2.1 A x.2.2 ∧ cutoff < ((S x.2.1 A x.2.2).card:ℝ) ∧
        ((G.interedges (x.1∩S x.2.1 A x.2.2) (x.1\S x.2.1 A x.2.2)).card:ℝ) ≤
          fraction x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2))) ≤
      exp ((t:ℝ)*binEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge := by
  have hpoint (T : Finset V) (hT : T.card=t) (A : Finset V) (hA : A⊆T) (xi : Ξ)
      (hel : eligible T A xi) :
      (fixedSizeLaw (univ\T) (N-t)).prob (fun R =>
        ((G.interedges ((T∪R)∩S T A xi) ((T∪R)\S T A xi)).card:ℝ) ≤
          fraction T A xi*(M T A xi*(p:ℝ)^2)) ≤
        if ((S T A xi).card:ℝ) ≤ cutoff then etaSmall else etaLarge := by
    have hcard : (univ\T).card=Fintype.card V-t := by
      rw [card_sdiff_of_subset (subset_univ T),card_univ,hT]
    exact fixed_remaining_cut_label_tail G (S T A xi) T p (by rw [hcard]; omega)
      (by rwa [hcard]) hp hp0 (hvalid T hT A hA xi hel)
  apply fixed_marked_two_label_regimes (univ:Finset V) (by simpa using hN) ht kap
    (fun U T xi A => eligible T A xi ∧ ((S T A xi).card:ℝ) ≤ cutoff ∧
      ((G.interedges (U∩S T A xi) (U\S T A xi)).card:ℝ) ≤ fraction T A xi*(M T A xi*(p:ℝ)^2))
    (fun U T xi A => eligible T A xi ∧ cutoff < ((S T A xi).card:ℝ) ∧
      ((G.interedges (U∩S T A xi) (U\S T A xi)).card:ℝ) ≤ fraction T A xi*(M T A xi*(p:ℝ)^2))
    hr hrhalf heS
  · intro T _ hT xi A hA _
    by_cases hel : eligible T A xi
    · by_cases hs : ((S T A xi).card:ℝ) ≤ cutoff
      · have hb := hpoint T hT A hA xi hel
        rw [if_pos hs] at hb
        exact (FiniteLaw.prob_mono _ (fun _ h => h.2.2)).trans hb
      · simpa only [hs,false_and,and_false,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heS
    · simpa only [hel,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heS
  · intro T _ hT xi A hA
    by_cases hel : eligible T A xi
    · by_cases hs : cutoff < ((S T A xi).card:ℝ)
      · have hb := hpoint T hT A hA xi hel
        rw [if_neg (not_le.mpr hs)] at hb
        exact (FiniteLaw.prob_mono _ (fun _ h => h.2.2)).trans hb
      · simpa only [hs,false_and,and_false,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heL
    · simpa only [hel,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const] using heL

end
end Cycle12
