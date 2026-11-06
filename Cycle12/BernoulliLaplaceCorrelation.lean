import Cycle12.BernoulliHarris
import Cycle12.BernoulliConditioning
import Cycle12.FiniteLaplace

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem exp_neg_mul_antitone {f : Finset V → ℝ} (hf : Monotone f)
    {s : ℝ} (hs : 0 ≤ s) : Antitone (fun S => exp (-s*f S)) := by
  intro A B hAB
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (hf hAB) (neg_nonpos.mpr hs)

/-- Conditioning a conjunction in a product measure, then separating its
dependent and disjoint summands. No conditional independence is assumed. -/
theorem bernoulli_indicator_laplace_lower (D A : Finset V) (hA : A⊆D)
    (p : unitInterval) (X Y Z : Finset V → ℝ)
    (hX : ∀ S, X S=Y S+Z S) (hY : Monotone Y) (hZ : Monotone Z)
    (hY0 : ∀ S, 0 ≤ Y S) (hZA : ∀ S, Z S=Z (S\A))
    (s : ℝ) (hs : 0 ≤ s) :
    (p:ℝ)^A.card * exp (-s*(subsetBernoulli (D\A) p).expect (fun R => Y (A∪R))) *
      finiteLaplace (subsetBernoulli D p) X s ≤
    (subsetBernoulli D p).expect (fun S => containsIndicator A S*exp (-s*X S)) := by
  have hunion (R : Finset V) : Z (A∪R)=Z R := by
    have he : (A∪R)\A=R\A := by
      ext v
      simp only [mem_sdiff,mem_union]
      tauto
    rw [hZA (A∪R),he,← hZA R]
  have hcond := bernoulli_condition_expect D A hA p (fun S => exp (-s*X S))
  change (subsetBernoulli D p).expect (fun S => containsIndicator A S*exp (-s*X S))=_ at hcond
  rw [hcond]
  have hj := finite_expect_exp_jensen (subsetBernoulli (D\A) p) (fun R => -s*Y (A∪R))
  rw [FiniteLaw.expect_const_mul] at hj
  have hmono : Monotone (fun R => Y (A∪R)) := by
    intro R T hRT
    exact hY (union_subset_union (Subset.refl A) hRT)
  have hh := subset_bernoulli_harris_antitone (D\A) p
    (fun R => exp (-s*Y (A∪R))) (fun R => exp (-s*Z R))
    (exp_neg_mul_antitone hmono hs) (exp_neg_mul_antitone hZ hs)
  have hsmall : finiteLaplace (subsetBernoulli D p) X s ≤
      (subsetBernoulli (D\A) p).expect (fun R => exp (-s*Z R)) := by
    calc
      _ ≤ (subsetBernoulli D p).expect (fun R => exp (-s*Z R)) := by
        apply FiniteLaw.expect_mono
        intro R
        apply exp_le_exp.mpr
        rw [hX R]
        nlinarith [hY0 R]
      _ = _ := subset_bernoulli_ignore_coordinates D A hA p _ (fun R => by rw [hZA R])
  have hnonneg : 0 ≤ (subsetBernoulli (D\A) p).expect (fun R => exp (-s*Z R)) :=
    FiniteLaw.expect_nonneg _ (fun _ => (exp_pos _).le)
  calc
    _ = (p:ℝ)^A.card*(exp (-s*(subsetBernoulli (D\A) p).expect (fun R => Y (A∪R))) *
        finiteLaplace (subsetBernoulli D p) X s) := by ring
    _ ≤ (p:ℝ)^A.card*((subsetBernoulli (D\A) p).expect (fun R => exp (-s*Y (A∪R))) *
        (subsetBernoulli (D\A) p).expect (fun R => exp (-s*Z R))) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg p.2.1 _)
      exact mul_le_mul hj hsmall (finite_laplace_nonneg _ _ _)
        (FiniteLaw.expect_nonneg _ (fun _ => (exp_pos _).le))
    _ ≤ (p:ℝ)^A.card*(subsetBernoulli (D\A) p).expect
        (fun R => exp (-s*Y (A∪R))*exp (-s*Z R)) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg p.2.1 _)
    _ = _ := by
      congr 1
      apply congrArg (FiniteLaw.expect _)
      funext R
      rw [← exp_add,hX,hunion]
      congr 1
      ring

end
end Cycle12
