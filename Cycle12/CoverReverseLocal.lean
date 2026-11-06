import Cycle12.CoverEntropyExponent

namespace Cycle12
open Real
noncomputable section

theorem cover_reverse_local_mean {p z R n t residual ps Y M : ℝ}
    (hp : 0 < p) (hR : 0 < R) (hps : 0 < ps) (hM : 0 ≤ M)
    (hn : n=R*(z/p)) (ht : t ≤ M*R) (hres : ps*p ≤ residual)
    (hgap : 0 < Y*z-p*M) :
    0 < ps*(Y*z-p*M)*R ∧ ps*(Y*z-p*M)*R ≤ residual*(Y*n-t) := by
  have hsize : 0 < Y*n-M*R := by
    rw [hn]
    have he : Y*(R*(z/p))-M*R=(R/p)*(Y*z-p*M) := by field_simp <;> ring
    rw [he]
    exact mul_pos (div_pos hR hp) hgap
  have hsize0 : 0 ≤ Y*n-t := by linarith only [hsize,ht]
  have hfirst := mul_le_mul_of_nonneg_left (sub_le_sub_left ht (Y*n)) (mul_pos hps hp).le
  have hsecond := mul_le_mul_of_nonneg_right hres hsize0
  have he : (ps*p)*(Y*n-M*R)=ps*(Y*z-p*M)*R := by rw [hn]; field_simp <;> ring
  rw [he] at hfirst
  exact ⟨mul_pos (mul_pos hps hgap) hR,hfirst.trans hsecond⟩

theorem cover_reverse_local_cutoff {p z R N ps Y M eta frac cap : ℝ}
    (hp : 0 < p) (hz : 0 < z) (hR : 0 < R) (hps : 0 < ps) (heta : 0 ≤ eta)
    (hN : N=z*R) (hcap : frac ≤ cap) (hgap : 0 < Y*z-p*M)
    (hbudget : (1+cap)*eta ≤ (49/100)*ps*(Y-M*p/z)) :
    (1+frac)*eta*N < (1/2)*(ps*(Y*z-p*M)*R) := by
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hc : (1+frac)*eta ≤ (1+cap)*eta := mul_le_mul_of_nonneg_right (add_le_add le_rfl hcap) heta
  have hs := mul_le_mul_of_nonneg_right (hc.trans hbudget) hN0
  have he : ((49/100)*ps*(Y-M*p/z))*N=(49/100)*(ps*(Y*z-p*M)*R) := by
    rw [hN]
    field_simp
    <;> ring
  rw [he] at hs
  have hpos := mul_pos (mul_pos hps hgap) hR
  linarith only [hs,hpos]

theorem cover_reverse_local_gap_lower {p pmax z zlo Y M : ℝ}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (hp : p ≤ pmax) (hz : zlo ≤ z) :
    Y*zlo-pmax*M ≤ Y*z-p*M := by
  have h₁ := mul_le_mul_of_nonneg_left hz hY
  have h₂ := mul_le_mul_of_nonneg_right hp hM
  linarith only [h₁,h₂]

theorem cover_reverse_local_tail {R z p ps Y M cc logUpper : ℝ} {t : ℕ}
    (hR : 0 ≤ R) (ht : (t:ℝ) ≤ M*R) (hlog : log 2 ≤ logUpper)
    (hbudget : cc ≤ ps*(Y*z-p*M)/8-M*logUpper) :
    (2:ℝ)^t*exp (-(1-(1/2:ℝ))^2*(ps*(Y*z-p*M)*R)/2) ≤ exp (-cc*R) := by
  have hlu : 0 ≤ logUpper := (log_pos (by norm_num : (1:ℝ) < 2)).le.trans hlog
  have hlabel := (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) t)).trans
    (mul_le_mul_of_nonneg_right ht hlu)
  have hbud := mul_le_mul_of_nonneg_right hbudget hR
  rw [cover_all_labels_exp,← exp_add]
  apply exp_le_exp.mpr
  nlinarith only [hlabel,hbud]

end
end Cycle12
