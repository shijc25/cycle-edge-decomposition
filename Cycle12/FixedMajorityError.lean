import Cycle12.SubsetVoteError

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_subset_copied_error_mean (D N A : Finset V) (v : V)
    (hD : D.Nonempty) (hN : N⊆D) (hN3 : 3 ≤ N.card)
    {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).expect (fun T => (subsetVoteLaw (T∩N)).prob (subsetCopiedError T A v)) ≤
      lowPositiveVoteProbability D N k*
          (((if v∈A then N\A else N∩A).card:ℝ)/N.card)+
        (1-lowPositiveVoteProbability D N k)*majorityCorrection N.card*
          majorityPolynomial (((if v∈A then N\A else N∩A).card:ℝ)/N.card)+
        if v∈A then exp (-(k:ℝ)*N.card/D.card) else 0 := by
  have hB : (if v∈A then N\A else N∩A)⊆N := by split_ifs <;> simp
  have hm := fixed_subset_vote_majority_mean D N (if v∈A then N\A else N∩A) hN hB hN3 hk
  have he := (fixedSizeLaw D k).expect_mono (fun T => subset_vote_error_bound N T A v)
  rw [FiniteLaw.expect_add] at he
  have hz : (fixedSizeLaw D k).expect (fun T => if T∩N=∅ then (1:ℝ) else 0) ≤
      exp (-(k:ℝ)*N.card/D.card) := by
    have hh := fixed_sample_miss_exponential D N hD hN hk
    convert hh using 1
    unfold FiniteLaw.prob
    congr 1
    funext T
    split_ifs <;> rfl
  by_cases hv : v∈A
  · simp only [hv,ite_true] at he hm ⊢
    linarith only [he,hm,hz]
  · simp only [hv,ite_false,FiniteLaw.expect_const] at he hm ⊢
    linarith only [he,hm]

end
end Cycle12
