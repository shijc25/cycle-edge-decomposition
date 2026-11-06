import Cycle12.RoundedProfileRetention
import Cycle12.RoundedJansonRate

namespace Cycle12
noncomputable section

def coverJansonDenominator (lambda kappa nu pmax zlo ps : ℝ) : ℝ :=
  min (lambda+1) (lambda+pmax/(nu*zlo)+kappa/(lambda*nu))+1/(ps*nu*zlo)

theorem cover_rounded_loss_upper {R z p Dlo zlo pmax M nu lambda : ℝ}
    (hR : 0 ≤ R) (hp : 0 < p) (hD : 0 < Dlo) (hzlo : 0 < zlo) (hz : zlo ≤ z)
    (hDz : Dlo*R ≤ z) (hpu : p ≤ pmax) (hM : 0 ≤ M) (hn : 0 < nu) (hl : 0 ≤ lambda) :
    (M*R)/(z/p)*(lambda+1/(nu*(z/p))) ≤
      (M*pmax/Dlo)*(lambda+pmax/(nu*zlo)) := by
  have hzp := hzlo.trans_le hz
  have hpp := hp.le.trans hpu
  have hleft : (M*R)/(z/p) ≤ M*pmax/Dlo := by
    have hId : (M*R)/(z/p)=(M*p*R)/z := by field_simp <;> ring
    rw [hId]
    apply (div_le_div_iff₀ hzp hD).mpr
    have hm := mul_le_mul_of_nonneg_left hDz (mul_nonneg hM hpp)
    have hmp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpu hM)
      (mul_nonneg hR hD.le)
    nlinarith only [hm,hmp]
  have hright : 1/(nu*(z/p)) ≤ pmax/(nu*zlo) := by
    have hId : 1/(nu*(z/p))=p/(nu*z) := by field_simp
    rw [hId]
    exact (div_le_div_of_nonneg_right hpu (mul_pos hn hzp).le).trans
      (div_le_div_of_nonneg_left hpp (mul_pos hn hzlo) (mul_le_mul_of_nonneg_left hz hn.le))
  exact mul_le_mul hleft (add_le_add le_rfl hright) (by positivity) (by positivity)

theorem cover_janson_denominator_pos {lambda kappa nu pmax zlo ps : ℝ}
    (hl : 1 ≤ lambda) (hk : 0 ≤ kappa) (hn : 0 < nu) (hp : 0 ≤ pmax)
    (hz : 0 < zlo) (hps : 0 < ps) : 0 < coverJansonDenominator lambda kappa nu pmax zlo ps := by
  unfold coverJansonDenominator
  have hl0 : 0 < lambda := by linarith only [hl]
  have hfirst : 0 < lambda+1 := by linarith only [hl]
  have hsecond : 0 < lambda+pmax/(nu*zlo)+kappa/(lambda*nu) := by positivity
  exact add_pos (lt_min hfirst hsecond) (by positivity)

theorem cover_janson_denominator_upper {lambda kappa nu p pmax z zlo ps residual : ℝ}
    (hl : 1 ≤ lambda) (hk : 0 ≤ kappa) (hn : 0 < nu) (hp : 0 < p) (hpu : p ≤ pmax)
    (hzlo : 0 < zlo) (hz : zlo ≤ z) (hps : 0 < ps) (hres : ps*p ≤ residual) :
    roundedJansonDenominator lambda kappa (z/p) residual (nu*(z/p)) ≤
      coverJansonDenominator lambda kappa nu pmax zlo ps := by
  have hzp := hzlo.trans_le hz
  have hpp := hp.le.trans hpu
  have hlp : 0 < lambda := by linarith only [hl]
  have hid1 : 1/(nu*(z/p))=p/(nu*z) := by field_simp
  have hid2 : kappa*(z/p)/(lambda*(nu*(z/p)))=kappa/(lambda*nu) := by field_simp
  have hsmall : 1/(nu*(z/p)) ≤ pmax/(nu*zlo) := by
    rw [hid1]
    exact (div_le_div_of_nonneg_right hpu (mul_pos hn hzp).le).trans
      (div_le_div_of_nonneg_left hpp (mul_pos hn hzlo) (mul_le_mul_of_nonneg_left hz hn.le))
  have hresProd : ps*nu*zlo ≤ residual*(nu*(z/p)) := by
    have hh := mul_le_mul_of_nonneg_right hres (by positivity : 0 ≤ nu*(z/p))
    have hz' := mul_le_mul_of_nonneg_left hz (mul_pos hps hn).le
    have hid : ps*p*(nu*(z/p))=ps*nu*z := by field_simp
    rw [hid] at hh
    exact hz'.trans hh
  have hlast := one_div_le_one_div_of_le (mul_pos (mul_pos hps hn) hzlo) hresProd
  unfold roundedJansonDenominator coverJansonDenominator
  rw [hid2]
  exact add_le_add (min_le_min le_rfl (by linarith only [hsmall])) hlast

theorem cover_janson_rate_lower {phi gamma lambda kappa nu p pmax z zlo ps residual : ℝ}
    (hphi : 0 ≤ phi) (hl : 1 ≤ lambda) (hk : 0 ≤ kappa) (hn : 0 < nu)
    (hp : 0 < p) (hpu : p ≤ pmax) (hzlo : 0 < zlo) (hz : zlo ≤ z)
    (hps : 0 < ps) (hres : ps*p ≤ residual)
    (hgamma : gamma ≤ phi*kappa*ps/coverJansonDenominator lambda kappa nu pmax zlo ps) :
    gamma*z ≤ phi*kappa*(z/p)*residual/
      roundedJansonDenominator lambda kappa (z/p) residual (nu*(z/p)) := by
  have hzp := hzlo.trans_le hz
  have hres0 := (mul_pos hps hp).trans_le hres
  have hden := cover_janson_denominator_upper hl hk hn hp hpu hzlo hz hps hres
  have hden0 := rounded_janson_denominator_pos hl hk (div_pos hzp hp).le hres0 (mul_pos hn (div_pos hzp hp))
  have hcap0 := cover_janson_denominator_pos hl hk hn (hp.le.trans hpu) hzlo hps
  have hnumerator : phi*kappa*ps*z ≤ phi*kappa*(z/p)*residual := by
    have hh := mul_le_mul_of_nonneg_left hres (mul_nonneg (mul_nonneg hphi hk) (div_pos hzp hp).le)
    have hid : (phi*kappa*(z/p))*(ps*p)=phi*kappa*ps*z := by field_simp <;> ring
    rwa [hid] at hh
  calc
    _ ≤ (phi*kappa*ps/coverJansonDenominator lambda kappa nu pmax zlo ps)*z :=
      mul_le_mul_of_nonneg_right hgamma hzp.le
    _ = (phi*kappa*ps*z)/coverJansonDenominator lambda kappa nu pmax zlo ps := by ring
    _ ≤ (phi*kappa*(z/p)*residual)/coverJansonDenominator lambda kappa nu pmax zlo ps :=
      div_le_div_of_nonneg_right hnumerator hcap0.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden0 hden

end
end Cycle12
