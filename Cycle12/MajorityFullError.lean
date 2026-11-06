import Cycle12.FixedMajorityJointCost

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem majority_polynomial_linear_bound {rho : ℝ} (hr : 0 ≤ rho) :
    majorityPolynomial rho ≤ (9/8:ℝ)*rho := by
  unfold majorityPolynomial
  nlinarith [mul_nonneg hr (sq_nonneg (rho-3/4))]

/-- A pointwise unweighted error bound. It needs no stability of the cut
and is also valid when the vertex lies outside the sampled ground set. -/
theorem fixed_majority_full_vertex_error (G : SimpleGraph V) (D U A : Finset V)
    (hU : U.Nonempty) {v : V} (hvD : v∈D) {k : ℕ} (hk : k ≤ U.card)
    {delta lambda Kfull : ℝ} (hdelta : 2 < delta)
    (hdeg : delta ≤ ((neighborsIn G v U).card:ℝ))
    (hmean : lambda ≤ ((k:ℝ)/U.card)*delta)
    (hK : 1 ≤ Kfull) (hcor : majorityCorrection delta*(9/8) ≤ Kfull) :
    (fixedSizeLaw U k).expect (fun T => (fixedMajorityLaw G T).prob
      (fun xi => ¬(v∈A ↔ v∈fixedMajoritySide D T (A∩T) xi))) ≤
      Kfull*((if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card:ℝ)/delta+
        exp (-lambda) := by
  let N := neighborsIn G v U
  let B := if v∈A then N\A else N∩A
  let a := lowPositiveVoteProbability U N k
  have hd0 : 0 < delta := by linarith
  have hn0 : (0:ℝ) < N.card := hd0.trans_le hdeg
  have hN3 : 3 ≤ N.card := by
    have hn : (2:ℝ) < N.card := hdelta.trans_le hdeg
    have hn' : 2 < N.card := by exact_mod_cast hn
    omega
  have hB : B⊆N := by dsimp [B]; split_ifs <;> simp
  have hr0 : 0 ≤ (B.card:ℝ)/N.card := by positivity
  have hr1 : (B.card:ℝ)/N.card ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast card_le_card hB)
  have ha0 : 0 ≤ a := low_positive_vote_nonneg U N k
  have ha1 : a ≤ 1 := FiniteLaw.prob_le_one _ _
  have hc0 : 0 ≤ majorityCorrection (N.card:ℝ) := by
    unfold majorityCorrection
    have hn : (2:ℝ) < N.card := hdelta.trans_le hdeg
    apply div_nonneg (sq_nonneg _)
    nlinarith only [hn]
  have hcor' : majorityCorrection (N.card:ℝ)*(9/8) ≤ Kfull :=
    (mul_le_mul_of_nonneg_right (majority_correction_antitone hdelta hdeg) (by norm_num)).trans hcor
  have hpure : majorityCorrection (N.card:ℝ)*majorityPolynomial ((B.card:ℝ)/N.card) ≤
      Kfull*((B.card:ℝ)/N.card) := by
    calc
      _ ≤ majorityCorrection (N.card:ℝ)*((9/8)*((B.card:ℝ)/N.card)) :=
        mul_le_mul_of_nonneg_left (majority_polynomial_linear_bound hr0) hc0
      _ = (majorityCorrection (N.card:ℝ)*(9/8))*((B.card:ℝ)/N.card) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcor' hr0
  have hlinear : a*((B.card:ℝ)/N.card) ≤ a*(Kfull*((B.card:ℝ)/N.card)) :=
    mul_le_mul_of_nonneg_left (by nlinarith only [hK,hr0]) ha0
  have htriple := mul_le_mul_of_nonneg_left hpure (sub_nonneg.mpr ha1)
  have htail : (if v∈A then exp (-(k:ℝ)*N.card/U.card) else 0) ≤ exp (-lambda) := by
    split_ifs
    · apply exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hdeg (show 0 ≤ (k:ℝ)/U.card by positivity)
      calc
        -(k:ℝ)*N.card/U.card = -((k:ℝ)/U.card*N.card) := by ring
        _ ≤ -lambda := neg_le_neg (hmean.trans hm)
    · exact (exp_pos _).le
  have hbound := fixed_majority_graph_error_mean G D U A hU hvD hN3 hk
  change _ ≤ a*((B.card:ℝ)/N.card)+(1-a)*majorityCorrection N.card*
    majorityPolynomial ((B.card:ℝ)/N.card)+(if v∈A then exp (-(k:ℝ)*N.card/U.card) else 0) at hbound
  have hden := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) B.card) hd0 hdeg)
    (show 0 ≤ Kfull by linarith only [hK])
  change _ ≤ Kfull*(B.card:ℝ)/delta+exp (-lambda)
  change Kfull*((B.card:ℝ)/N.card) ≤ Kfull*((B.card:ℝ)/delta) at hden
  simp only [div_eq_mul_inv] at hbound hlinear htriple htail hden ⊢
  nlinarith only [hbound,hlinear,htriple,htail,hden]

end
end Cycle12
