import Cycle12.ThreeVoteCounting

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def majorityPolynomial (rho : ℝ) : ℝ := 3*rho^2-2*rho^3
def majorityCorrection (d : ℝ) : ℝ := d^2/((d-1)*(d-2))

theorem distinct_triples_nonempty (D : Finset V) (hD : 3 ≤ D.card) :
    (distinctTriples D).Nonempty := by
  apply card_pos.mp
  rw [distinct_triples_card]
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

/-- Uniformly ordered three distinct votes, rather than independent draws. -/
def threeVoteLaw (D : Finset V) (hD : 3 ≤ D.card) : FiniteLaw (V×V×V) :=
  FiniteLaw.uniformOn (distinctTriples D) (distinct_triples_nonempty D hD)

theorem three_vote_majority_probability (D B : Finset V)
    (hD : 3 ≤ D.card) (hB : B⊆D) :
    (threeVoteLaw D hD).prob (tripleMajority B) ≤
      majorityCorrection D.card*majorityPolynomial ((B.card:ℝ)/D.card) := by
  have hcount := distinct_triple_majority_card_le D B hB
  have hnum : (((distinctTriples D).filter (tripleMajority B)).card:ℝ) ≤
      (B.card:ℝ)^2*D.card+2*(B.card*((D.card:ℝ)-B.card)*B.card) := by
    have hh := (Nat.cast_le (α:=ℝ)).mpr hcount
    push_cast [Nat.cast_sub (card_le_card hB)] at hh
    nlinarith only [hh]
  have hd : (2:ℝ)<D.card := by exact_mod_cast (show 2<D.card by omega)
  have hd0 : (D.card:ℝ)≠0 := ne_of_gt (by linarith only [hd])
  have hd1 : (D.card:ℝ)-1≠0 := ne_of_gt (by linarith only [hd])
  have hd2 : (D.card:ℝ)-2≠0 := ne_of_gt (by linarith only [hd])
  have hden : ((distinctTriples D).card:ℝ)=(D.card:ℝ)*(D.card-1)*(D.card-2) := by
    rw [distinct_triples_card,Nat.cast_mul,Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ D.card),Nat.cast_sub (by omega : 2 ≤ D.card)]
    norm_num
  unfold threeVoteLaw FiniteLaw.prob
  rw [FiniteLaw.uniformOn_expect]
  simp only [sum_boole]
  rw [hden]
  calc
    _ ≤ ((B.card:ℝ)^2*D.card+2*(B.card*((D.card:ℝ)-B.card)*B.card))/
        ((D.card:ℝ)*(D.card-1)*(D.card-2)) :=
      div_le_div_of_nonneg_right hnum
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith only [hd]))
          (by linarith only [hd]))
    _ = _ := by
      unfold majorityCorrection majorityPolynomial
      field_simp
      <;> ring

theorem majority_polynomial_nonneg {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho ≤ 1) :
    0 ≤ majorityPolynomial rho := by
  have he : majorityPolynomial rho=rho^2*(3-2*rho) := by unfold majorityPolynomial; ring
  rw [he]
  exact mul_nonneg (sq_nonneg _) (by linarith only [h1])

theorem majority_correction_antitone {delta d : ℝ} (hdelta : 2<delta) (hd : delta ≤ d) :
    majorityCorrection d ≤ majorityCorrection delta := by
  have hp : 0<(d-1)*(d-2) := mul_pos (by linarith) (by linarith)
  have hq : 0<(delta-1)*(delta-2) := mul_pos (by linarith) (by linarith)
  unfold majorityCorrection
  apply (div_le_div_iff₀ hp hq).mpr
  have hfactor : 0 ≤ 3*d*delta-2*d-2*delta := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hd) (show 0 ≤ 3*delta-2 by linarith)
    have h₂ := mul_nonneg (show 0 ≤ delta by linarith) (show 0 ≤ 3*delta-4 by linarith)
    nlinarith only [h₁,h₂]
  have hprod := mul_nonneg (sub_nonneg.mpr hd) hfactor
  nlinarith only [hprod]

theorem three_vote_majority_probability_min_degree (D B : Finset V)
    (hD : 3 ≤ D.card) (hB : B⊆D) {delta : ℝ}
    (hdelta : 2<delta) (hd : delta ≤ D.card) :
    (threeVoteLaw D hD).prob (tripleMajority B) ≤
      majorityCorrection delta*majorityPolynomial ((B.card:ℝ)/D.card) := by
  have hpos : (0:ℝ)<D.card := (by linarith : 0<delta).trans_le hd
  have hr0 : (0:ℝ) ≤ (B.card:ℝ)/D.card := div_nonneg (Nat.cast_nonneg _) hpos.le
  have hr1 : (B.card:ℝ)/D.card ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast card_le_card hB)
  exact (three_vote_majority_probability D B hD hB).trans
    (mul_le_mul_of_nonneg_right (majority_correction_antitone hdelta hd)
      (majority_polynomial_nonneg hr0 hr1))

end
end Cycle12
