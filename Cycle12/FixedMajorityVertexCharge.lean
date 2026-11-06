import Cycle12.FixedMajorityClassifier
import Cycle12.JointMajorityBound

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_majority_vertex_charge (G : SimpleGraph V) (D U A : Finset V)
    (hU : U.Nonempty) {v : V} (hvD : v∈D) {k : ℕ} (hk : k ≤ U.card)
    {z dm tau lambda K : ℝ} (hz : 0<z) (hdm : 0<dm) (htau : 0 ≤ tau)
    (hdelta : 2<dm*z) (hdeg : dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hlambda : 3 ≤ lambda) (hmean : lambda ≤ ((k:ℝ)/U.card)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1+tau/dm-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1+tau/dm-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K) :
    (((neighborsIn G v U).card:ℝ)-
      (if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card+tau*z)*
        (fixedSizeLaw U k).expect (fun T => (fixedMajorityLaw G T).prob
          (fun xi => ¬(v∈A ↔ v∈fixedMajoritySide D T (A∩T) xi))) ≤
      K*(if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card+
        if v∈A then (dm*z+tau*z)*exp (-((k:ℝ)/U.card)*(dm*z)) else 0 := by
  let N := neighborsIn G v U
  let B := if v∈A then N\A else N∩A
  let d : ℝ := N.card
  let b : ℝ := B.card
  let a := lowPositiveVoteProbability U N k
  let p : ℝ := (k:ℝ)/U.card
  have hN : N⊆U := filter_subset _ _
  have hB : B⊆N := by dsimp [B]; split_ifs <;> simp
  have hd : (2:ℝ)<d := hdelta.trans_le hdeg
  have hd0 : 0<d := by linarith only [hd]
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have hbd : b ≤ d := by
    change (B.card:ℝ) ≤ N.card
    exact_mod_cast card_le_card hB
  have hr0 : 0 ≤ b/d := div_nonneg hb0 hd0.le
  have hr1 : b/d ≤ 1 := (div_le_one hd0).mpr hbd
  have hN3 : 3 ≤ N.card := by
    have hn : (2:ℝ)<N.card := hd
    have hn' : 2<N.card := by exact_mod_cast hn
    omega
  have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcount : lambda ≤ (k:ℝ)*N.card/U.card := by
    have hh := mul_le_mul_of_nonneg_left hdeg hp0
    dsimp [p] at hh
    calc
      _ ≤ ((k:ℝ)/U.card)*(dm*z) := hmean
      _ ≤ ((k:ℝ)/U.card)*N.card := hh
      _ = _ := by ring
  have ha0 : 0 ≤ a := low_positive_vote_nonneg U N k
  have ha1 : a ≤ 1 := FiniteLaw.prob_le_one _ _
  have haa : a ≤ min 1 (poissonTailTwo lambda) := low_positive_vote_poisson U N hN hk hlambda hcount
  have hactual := fixed_majority_graph_error_mean G D U A hU hvD hN3 hk
  have hcorrection := majority_correction_antitone hdelta hdeg
  have hpoly := majority_polynomial_nonneg hr0 hr1
  have hscale := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcorrection hpoly) (sub_nonneg.mpr ha1)
  have hzero : 0 ≤ (if v∈A then exp (-(k:ℝ)*N.card/U.card) else 0) := by
    split_ifs <;> positivity
  have hbound : (fixedSizeLaw U k).expect (fun T => (fixedMajorityLaw G T).prob
      (fun xi => ¬(v∈A ↔ v∈fixedMajoritySide D T (A∩T) xi))) ≤
      a*(b/d)+(1-a)*majorityCorrection (dm*z)*majorityPolynomial (b/d)+
        (if v∈A then exp (-(k:ℝ)*N.card/U.card) else 0) := by
    change _ ≤ a*(b/d)+(1-a)*majorityCorrection d*majorityPolynomial (b/d)+
      (if v∈A then exp (-(k:ℝ)*N.card/U.card) else 0) at hactual
    linarith only [hactual,hscale]
  have hv := majority_joint_vertex_bound hz hdm htau hdeg hb0 hbd ha0 haa hzero hK hbound
    (hpure _ hr0 hr1) (hmixed _ hr0 hr1)
  change (d-b+tau*z)*_ ≤ K*b+_ at hv ⊢
  apply hv.trans
  have hmark : 1 ≤ p*(dm*z+tau*z) := by
    have hterm : 0 ≤ p*(tau*z) := mul_nonneg hp0 (mul_nonneg htau hz.le)
    change lambda ≤ p*(dm*z) at hmean
    nlinarith only [hmean,hlambda,hterm]
  by_cases hvA : v∈A
  · simp only [hvA,ite_true]
    have hexp : -(k:ℝ)*N.card/U.card= -p*d := by dsimp [p,d]; ring
    rw [hexp]
    simpa only [add_comm] using add_le_add_left (shifted_degree_exp_antitone hp0 hmark hdeg) (K*b)
  · simp only [hvA,ite_false,mul_zero,le_refl]

end
end Cycle12
