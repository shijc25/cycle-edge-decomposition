import Cycle12.Foundations.GraphCopyWitness
import Cycle12.Foundations.SubsetUpperChernoff
import Cycle12.Foundations.FiniteJointLaw

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem neighborCopy_witness_probability (G : SimpleGraph V) (U A : Finset V) (hAU : A⊆U)
    (p : unitInterval) {δ budget cap : ℝ} (hδ : 0<δ) (hmark : 1≤(p:ℝ)*δ)
    (hdeg : ∀ v∈U, δ≤((neighborsIn G v U).card:ℝ))
    (hbudget : 0<budget) (hμ : 0<(p:ℝ)*U.card) (hcap : (p:ℝ)*U.card≤cap) :
    1-(2*((G.interedges A (U\A)).card:ℝ)+δ*exp (-(p:ℝ)*δ)*A.card)/budget-
      exp (-(cap-(p:ℝ)*U.card)^2/(2*cap)) ≤
    (subsetBernoulli U p).expect (fun T => (neighborCopyLaw G T).prob (fun ξ =>
      sampledErrorWeight G U A (U∩copiedSide T ξ (A∩T))≤budget ∧ (T.card:ℝ)≤cap)) := by
  let μ := (subsetBernoulli U p).joint (neighborCopyLaw G)
  let X : Finset V×(V→Option V)→ℝ := fun x =>
    sampledErrorWeight G U A (U∩copiedSide x.1 x.2 (A∩x.1))
  have hX : ∀ x, 0≤X x := by
    intro x; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have he : μ.expect X ≤ 2*((G.interedges A (U\A)).card:ℝ)+δ*exp (-(p:ℝ)*δ)*A.card := by
    rw [FiniteLaw.expect_joint]
    exact neighborCopy_total_error G U A hAU p hδ hmark hdeg
  have hbad : μ.prob (fun x => cap<(x.1.card:ℝ)) ≤ exp (-(cap-(p:ℝ)*U.card)^2/(2*cap)) := by
    rw [FiniteLaw.prob_joint_fst (subsetBernoulli U p) (neighborCopyLaw G)
      (fun T : Finset V => cap<(T.card:ℝ))]
    exact (FiniteLaw.prob_mono _ (fun T h => h.le)).trans
      (subsetBernoulli_card_upper_tail U p hμ hcap)
  have hg := μ.prob_good_weight X (fun x => cap<(x.1.card:ℝ)) hX hbudget
  have hediv := div_le_div_of_nonneg_right he hbudget.le
  have htotal : 1-(2*((G.interedges A (U\A)).card:ℝ)+δ*exp (-(p:ℝ)*δ)*A.card)/budget-
      exp (-(cap-(p:ℝ)*U.card)^2/(2*cap)) ≤
      μ.prob (fun x => X x≤budget ∧ (x.1.card:ℝ)≤cap) := by
    simp only [not_lt] at hg
    linarith
  rw [FiniteLaw.prob_joint] at htotal
  exact htotal

theorem neighborCopy_cut_witness (G : SimpleGraph V) (U A : Finset V) (hAU : A⊆U)
    (ha : 0<(A.card:ℝ)) (p : unitInterval) {δ β err cap : ℝ}
    (hδ : 0<δ) (hmark : 1≤(p:ℝ)*δ)
    (hdeg : ∀ v∈U, δ≤((neighborsIn G v U).card:ℝ)) (herr : 0<err)
    (hbad : ((G.interedges A (U\A)).card:ℝ)≤β*A.card)
    (hμ : 0<(p:ℝ)*U.card) (hcap : (p:ℝ)*U.card≤cap) :
    1-(2*β+δ*exp (-(p:ℝ)*δ))/err-exp (-(cap-(p:ℝ)*U.card)^2/(2*cap)) ≤
    (subsetBernoulli U p).expect (fun T => (neighborCopyLaw G T).prob (fun ξ =>
      sampledErrorWeight G U A (U∩copiedSide T ξ (A∩T))≤err*A.card ∧ (T.card:ℝ)≤cap)) := by
  have hh := neighborCopy_witness_probability G U A hAU p hδ hmark hdeg
    (mul_pos herr ha) hμ hcap
  apply le_trans _ hh
  have hdiv : (2*((G.interedges A (U\A)).card:ℝ)+δ*exp (-(p:ℝ)*δ)*A.card)/(err*A.card) ≤
      (2*β+δ*exp (-(p:ℝ)*δ))/err := by
    apply (div_le_div_iff₀ (mul_pos herr ha) herr).mpr
    nlinarith [mul_le_mul_of_nonneg_right hbad herr.le]
  linarith

end
end Cycle13
