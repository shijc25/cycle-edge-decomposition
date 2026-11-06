import Cycle12.FixedMarkedUnion
import Cycle12.RoundedResidualJanson

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

/-- All label-dependent truncated graphs are tested in the original
fixed-size experiment. Each graph is determined before the residual sample
is exposed. The hypotheses are deterministic graph and scalar bounds. -/
theorem fixed_marked_truncated_cut_bound (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N)
    (kap : Finset V → FiniteLaw Ξ)
    (S : Finset V → Finset V → Ξ → Finset V)
    (lambda M tau : Finset V → Finset V → Ξ → ℝ)
    (eligible : Finset V → Finset V → Ξ → Prop)
    (p : unitInterval) (hp0 : 0<(p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    {eta : ℝ} (heta : 0 ≤ eta)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi, eligible T A xi →
      (S T A xi).Nonempty ∧ 1 ≤ lambda T A xi ∧ 0<M T A xi ∧
      M T A xi ≤ (Fintype.card
        (truncatedResidualGraph G (S T A xi) T (roundedCutCap (lambda T A xi) (S T A xi))).edgeSet:ℝ) ∧
      0 ≤ tau T A xi ∧ tau T A xi ≤ 1 ∧
      2*Real.exp (-fullJansonPhi (tau T A xi)*(M T A xi)*(p:ℝ)^2/
        (1+min ((lambda T A xi+1)*(S T A xi).card)
          (lambda T A xi*(S T A xi).card+1+M T A xi/(lambda T A xi*(S T A xi).card))*(p:ℝ))) ≤ eta) :
    (fixedMarkedExperiment (univ:Finset V) N t kap).prob (fun x =>
      ∃ A⊆x.2.1, eligible x.2.1 A x.2.2 ∧
        ((G.interedges (x.1∩S x.2.1 A x.2.2) (x.1\S x.2.1 A x.2.2)).card:ℝ) ≤
          tau x.2.1 A x.2.2*(M x.2.1 A x.2.2*(p:ℝ)^2)) ≤ (2:ℝ)^t*eta := by
  apply fixed_marked_uniform_label_bound (univ:Finset V) (by simpa using hN) ht kap
    (fun U T xi A => eligible T A xi ∧
      ((G.interedges (U∩S T A xi) (U\S T A xi)).card:ℝ) ≤ tau T A xi*(M T A xi*(p:ℝ)^2))
  intro T _ hT xi A hA
  by_cases hel : eligible T A xi
  · obtain ⟨hS,hl,hM,hret,ht0,ht1,hbudget⟩ := hvalid T hT A hA xi hel
    have hcard : (univ\T).card=Fintype.card V-t := by
      rw [card_sdiff_of_subset (subset_univ T),card_univ,hT]
    have hk : N-t ≤ (univ\T).card := by rw [hcard]; omega
    have hmp : ((univ\T).card:ℝ)*(p:ℝ)=((N-t:ℕ):ℝ) := by rwa [hcard]
    have hj := rounded_residual_sharp_janson G (S T A xi) T hS hl p hk hmp hp hp0
      hM hret (tau T A xi) ht0 ht1
    apply (le_trans _ hj).trans hbudget
    apply FiniteLaw.prob_mono
    intro R hR
    have hcut := sampled_truncated_residual_cut_le G (S T A xi) T (T∪R) R
      (roundedCutCap (lambda T A xi) (S T A xi)) subset_union_right
    exact (Nat.cast_le (α:=ℝ)).mpr hcut |>.trans hR.2
  · simpa only [hel,false_and,FiniteLaw.prob,if_false,FiniteLaw.expect_const] using heta

end
end Cycle12
