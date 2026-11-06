import Cycle12.RoundedResidualJanson
import Cycle12.JansonPhiSeries

namespace Cycle12
noncomputable section

def roundedJansonDenominator (lambda kappa h p u : ℝ) : ℝ :=
  min (lambda+1) (lambda+1/u+kappa*h/(lambda*u))+1/(p*u)

theorem rounded_janson_denominator_pos {lambda kappa h p u : ℝ}
    (hl : 1 ≤ lambda) (hk : 0 ≤ kappa) (hh : 0 ≤ h) (hp : 0 < p) (hu : 0 < u) :
    0 < roundedJansonDenominator lambda kappa h p u := by
  unfold roundedJansonDenominator
  have hl0 : 0 < lambda := by linarith
  have h₁ : 0 < lambda+1 := by linarith
  have h₂ : 0 < lambda+1/u+kappa*h/(lambda*u) := by positivity
  exact add_pos (lt_min h₁ h₂) (by positivity)

theorem rounded_janson_rate_normalize (phi kappa h lambda p u : ℝ)
    (hu : u≠0) (hp : p≠0) (hu0 : 0 ≤ u) :
    phi*(kappa*h*u)*p^2/
      (1+min ((lambda+1)*u) (lambda*u+1+(kappa*h*u)/(lambda*u))*p)=
      phi*kappa*h*p/roundedJansonDenominator lambda kappa h p u := by
  have he : min ((lambda+1)*u) (lambda*u+1+(kappa*h*u)/(lambda*u))=
      u*min (lambda+1) (lambda+1/u+kappa*h/(lambda*u)) := by
    rw [mul_min_of_nonneg _ _ hu0]
    congr 1
    · ring
    · field_simp
      <;> ring
  rw [he]
  have hd : 1+u*min (lambda+1) (lambda+1/u+kappa*h/(lambda*u))*p=
      (p*u)*roundedJansonDenominator lambda kappa h p u := by
    unfold roundedJansonDenominator
    field_simp
    <;> ring
  have hn : phi*(kappa*h*u)*p^2=(p*u)*(phi*kappa*h*p) := by ring
  rw [hd,hn]
  exact mul_div_mul_left _ _ (mul_ne_zero hp hu)

theorem rounded_janson_denominator_antitone {lambda kappa h p u0 u : ℝ}
    (hl : 0 < lambda) (hk : 0 ≤ kappa) (hh : 0 ≤ h) (hp : 0 < p)
    (hu0 : 0 < u0) (hu : u0 ≤ u) :
    roundedJansonDenominator lambda kappa h p u ≤
      roundedJansonDenominator lambda kappa h p u0 := by
  have hu' := hu0.trans_le hu
  have h₁ : 1/u ≤ 1/u0 := one_div_le_one_div_of_le hu0 hu
  have h₂ : kappa*h/(lambda*u) ≤ kappa*h/(lambda*u0) :=
    div_le_div_of_nonneg_left (mul_nonneg hk hh) (mul_pos hl hu0)
      (mul_le_mul_of_nonneg_left hu hl.le)
  have h₃ : 1/(p*u) ≤ 1/(p*u0) :=
    one_div_le_one_div_of_le (mul_pos hp hu0) (mul_le_mul_of_nonneg_left hu hp.le)
  exact add_le_add (min_le_min le_rfl (by linarith only [h₁,h₂])) h₃

/-- Uniform lower rate on a whole side-size bin, including its unbounded
last interval. Both possible dependency budgets are handled monotonically. -/
theorem rounded_janson_rate_lower {phiLower phi lambda kappa h p u0 u : ℝ}
    (hphi0 : 0 ≤ phiLower) (hphi : phiLower ≤ phi)
    (hl : 1 ≤ lambda) (hk : 0 ≤ kappa) (hh : 0 ≤ h) (hp : 0 < p)
    (hu0 : 0 < u0) (hu : u0 ≤ u) :
    phiLower*kappa*h*p/roundedJansonDenominator lambda kappa h p u0 ≤
      phi*(kappa*h*u)*p^2/
        (1+min ((lambda+1)*u) (lambda*u+1+(kappa*h*u)/(lambda*u))*p) := by
  have hu' := hu0.trans_le hu
  rw [rounded_janson_rate_normalize _ _ _ _ _ _ hu'.ne' hp.ne' hu'.le]
  have hd := rounded_janson_denominator_antitone (show 0 < lambda by linarith) hk hh hp hu0 hu
  have hpDen := rounded_janson_denominator_pos hl hk hh hp hu'
  have hnum : phiLower*kappa*h*p ≤ phi*kappa*h*p := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hphi hk) hh) hp.le
  calc
    _ ≤ phiLower*kappa*h*p/roundedJansonDenominator lambda kappa h p u :=
      div_le_div_of_nonneg_left (by positivity) hpDen hd
    _ ≤ _ := div_le_div_of_nonneg_right hnum hpDen.le

open Finset SimpleGraph Cycle13
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem rounded_residual_certified_tail (G : SimpleGraph V) (S T : Finset V)
    {lambda kappa h u0 phiLower rate : ℝ} (hl : 1 ≤ lambda) (hkappa : 0 < kappa)
    (hh : 0 < h) (hu0 : 0 < u0) (hside : u0 ≤ (S.card:ℝ))
    (p : unitInterval) {k : ℕ} (hk : k ≤ (univ\T).card)
    (hmean : ((univ\T).card:ℝ)*(p:ℝ)=(k:ℝ)) (hp : (p:ℝ) ≤ 1/2) (hp0 : 0 < (p:ℝ))
    (hret : kappa*h*S.card ≤
      (Fintype.card (truncatedResidualGraph G S T (roundedCutCap lambda S)).edgeSet:ℝ))
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (hphi0 : 0 ≤ phiLower) (hphi : phiLower ≤ fullJansonPhi tau)
    (hrate : rate ≤ phiLower*kappa*h*(p:ℝ)/roundedJansonDenominator lambda kappa h p u0) :
    (fixedSizeLaw (univ\T) k).prob (fun R =>
      (sampledFinsetEdgeCount (truncatedResidualGraph G S T (roundedCutCap lambda S)) R:ℝ) ≤
        tau*(kappa*h*S.card*(p:ℝ)^2)) ≤ 2*Real.exp (-rate) := by
  have hs : (0:ℝ) < S.card := hu0.trans_le hside
  have hS : S.Nonempty := card_pos.mp (by exact_mod_cast hs)
  have hm : 0 < kappa*h*S.card := mul_pos (mul_pos hkappa hh) hs
  have hj := rounded_residual_sharp_janson G S T hS hl p hk hmean hp hp0 hm hret tau ht0 ht1
  apply hj.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hb := hrate.trans (rounded_janson_rate_lower hphi0 hphi hl hkappa.le hh.le hp0 hu0 hside)
  simpa only [neg_mul,neg_div] using neg_le_neg hb

end
end Cycle12
