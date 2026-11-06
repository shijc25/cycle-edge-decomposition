import Cycle12.FixedMarkedCoupling
import Cycle12.FixedIntersectionDisintegration
import Cycle12.Foundations.SubsetBernoulliRecursion

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem subset_bernoulli_support (D S : Finset V) (p : unitInterval)
    (hS : 0<(subsetBernoulli D p).mass S) : S⊆D := by
  by_contra hn
  rw [subsetBernoulli_mass_not_subset D S p hn] at hS
  exact lt_irrefl _ hS

theorem bernoulli_condition_atom (D A S : Finset V) (hA : A⊆D) (p : unitInterval) :
    (subsetBernoulli D p).mass S*(if A⊆S then (1:ℝ) else 0)=
      (p:ℝ)^A.card*(if A⊆S then (subsetBernoulli (D\A) p).mass (S\A) else 0) := by
  by_cases hAS : A⊆S
  · rw [if_pos hAS,if_pos hAS,mul_one]
    by_cases hSD : S⊆D
    · rw [subsetBernoulli_mass D S p hSD,
        subsetBernoulli_mass (D\A) (S\A) p (sdiff_subset_sdiff_left A hSD),
        card_sdiff_of_subset hA,card_sdiff_of_subset hAS]
      have hc : S.card=A.card+(S.card-A.card) := by have hh := card_le_card hAS; omega
      have hr : D.card-A.card-(S.card-A.card)=D.card-S.card := by
        have h₁ := card_le_card hAS
        have h₂ := card_le_card hSD
        omega
      rw [hr]
      conv_lhs => rw [hc,pow_add]
      rw [← hc]
      ring
    · have hr : ¬S\A⊆D\A := by
        intro hr
        apply hSD
        intro v hv
        by_cases hvA : v∈A
        · exact hA hvA
        · exact (mem_sdiff.mp (hr (mem_sdiff.mpr ⟨hv,hvA⟩))).1
      rw [subsetBernoulli_mass_not_subset D S p hSD,
        subsetBernoulli_mass_not_subset (D\A) (S\A) p hr,mul_zero]
  · simp only [if_neg hAS,mul_zero]

/-- Exact conditioning on every member of A being selected, retaining a
factor p^|A| rather than dividing by it, so endpoint parameters remain valid. -/
theorem bernoulli_condition_expect (D A : Finset V) (hA : A⊆D) (p : unitInterval)
    (f : Finset V → ℝ) :
    (subsetBernoulli D p).expect (fun S => (if A⊆S then (1:ℝ) else 0)*f S)=
      (p:ℝ)^A.card*(subsetBernoulli (D\A) p).expect (fun R => f (A∪R)) := by
  unfold FiniteLaw.expect
  simp_rw [← mul_assoc,bernoulli_condition_atom D A _ hA p,mul_assoc]
  rw [← mul_sum]
  congr 1
  apply disjoint_remaining_union_expect
  intro R hR
  exact disjoint_of_subset_left (subset_bernoulli_support (D\A) R p hR) disjoint_sdiff_self_left

theorem subset_bernoulli_disjoint_union_expect (A B : Finset V) (hAB : Disjoint A B)
    (p : unitInterval) (f : Finset V → ℝ) :
    (subsetBernoulli (A∪B) p).expect f=
      (subsetBernoulli A p).expect (fun S => (subsetBernoulli B p).expect (fun T => f (S∪T))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp only [empty_union,subsetBernoulli_expect_empty]
  | @insert v A hv ih =>
    have hvB : v∉B := (disjoint_insert_left.mp hAB).1
    have hAB' : Disjoint A B := (disjoint_insert_left.mp hAB).2
    rw [insert_union,subsetBernoulli_expect_insert (A∪B) v (by simpa using And.intro hv hvB),
      subsetBernoulli_expect_insert A v hv,ih hAB' f,ih hAB' (fun S => f (insert v S))]
    simp only [insert_union]

/-- A statistic unchanged by deleting A has the same expectation after
removing A from the Bernoulli ground set. -/
theorem subset_bernoulli_ignore_coordinates (D A : Finset V) (hA : A⊆D)
    (p : unitInterval) (f : Finset V → ℝ) (hf : ∀ S, f S=f (S\A)) :
    (subsetBernoulli D p).expect f=(subsetBernoulli (D\A) p).expect f := by
  have hsplit := subset_bernoulli_disjoint_union_expect A (D\A) disjoint_sdiff_self_right p f
  rw [union_sdiff_of_subset hA] at hsplit
  rw [hsplit,← (subsetBernoulli A p).expect_const ((subsetBernoulli (D\A) p).expect f)]
  apply finite_expect_congr_support
  intro S hS
  have hSA := subset_bernoulli_support A S p hS
  apply finite_expect_congr_support
  intro T hT
  have hTA := subset_bernoulli_support (D\A) T p hT
  have hdis : Disjoint T A := disjoint_of_subset_left hTA disjoint_sdiff_self_left
  calc
    f (S∪T) = f ((S∪T)\A) := hf _
    _ = f T := by rw [union_sdiff_distrib,sdiff_eq_empty_iff_subset.mpr hSA,empty_union,
      sdiff_eq_left.mpr hdis]

end
end Cycle12
