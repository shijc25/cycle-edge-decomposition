import Cycle12.FixedSampleBernoulli
import Cycle12.BernoulliPoissonLimit

namespace Cycle12
open Polynomial Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

def poissonTailTwo (mu : ℝ) : ℝ := exp (-mu)*(1+mu+mu^2/2)

theorem poisson_tail_two_derivative (mu : ℝ) :
    HasDerivAt poissonTailTwo (-(mu^2*exp (-mu))/2) mu := by
  have he := (hasDerivAt_id mu).neg.exp
  have hp := ((hasDerivAt_const mu (1:ℝ)).add (hasDerivAt_id mu)).add
    (((hasDerivAt_id mu).pow 2).div_const 2)
  convert he.mul hp using 1 <;>
    norm_num [poissonTailTwo,Pi.neg_apply,Pi.add_apply,Pi.pow_apply]
  · funext x
    dsimp only [poissonTailTwo,Pi.mul_apply,Pi.add_apply,id_eq]
  · ring

theorem poisson_tail_two_antitone : Antitone poissonTailTwo := by
  apply antitone_of_deriv_nonpos
  · intro x
    exact (poisson_tail_two_derivative x).differentiableAt
  · intro x
    rw [(poisson_tail_two_derivative x).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) (exp_pos _).le)) (by norm_num)

theorem poisson_tail_two_nonneg {mu : ℝ} (hm : 0 ≤ mu) : 0 ≤ poissonTailTwo mu := by
  unfold poissonTailTwo
  positivity

theorem poisson_tail_two_le_one {mu : ℝ} (hm : 0 ≤ mu) : poissonTailTwo mu ≤ 1 := by
  simpa [poissonTailTwo] using poisson_tail_two_antitone hm

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Exact fixed-cardinality sampling: the probability of fewer than three
marked members is bounded by the Poisson lower CDF at any lower mean at least three. -/
theorem fixed_sample_low_vote_poisson (D B : Finset V) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {lambda : ℝ} (hlambda : 3 ≤ lambda)
    (hmean : lambda ≤ (k:ℝ)*B.card/D.card) :
    (fixedSizeLaw D k).prob (fun T => (T∩B).card<3) ≤ poissonTailTwo lambda := by
  obtain ⟨l,hl,heq,hsum⟩ := fixed_sample_exists_bernoulli_list D B hB hk
  have hmu : 3 ≤ l.sum := by rw [hsum]; exact hlambda.trans hmean
  have hh := bernoulli_small_tail_poisson l hl hmu
  rw [← heq,finite_count_small_tail] at hh
  change _ ≤ poissonTailTwo l.sum at hh
  exact hh.trans (poisson_tail_two_antitone (by rwa [hsum]))

theorem fixed_sample_low_vote_poisson_capped (D B : Finset V) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {lambda : ℝ} (hlambda : 3 ≤ lambda)
    (hmean : lambda ≤ (k:ℝ)*B.card/D.card) :
    (fixedSizeLaw D k).prob (fun T => (T∩B).card<3) ≤ min 1 (poissonTailTwo lambda) :=
  le_min (FiniteLaw.prob_le_one _ _) (fixed_sample_low_vote_poisson D B hB hk hlambda hmean)

end
end Cycle12
