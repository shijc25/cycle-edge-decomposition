import Cycle12.CoverMarkingRealization
import Cycle12.RationalDegreeEnvelope

namespace Cycle12

structure RatMarkedGeometry where
  inputs : RatMomentCertificate
  Rlo : ℚ
  zlo : ℚ
  Dlo : ℚ
  Wlo : ℚ
  qmark : ℚ
  dm : ℚ
  M : ℚ
  ps : ℚ
  pmax : ℚ

def RatMarkedGeometry.Valid (c : RatMarkedGeometry) : Prop :=
  0 < c.Rlo ∧ 0 < c.zlo ∧ 0 < c.Dlo ∧ 0 < c.Wlo ∧ 0 ≤ c.qmark ∧ 0 ≤ c.dm ∧
  0 ≤ c.inputs.pl ∧ 0 < c.ps ∧
  c.Rlo ≤ 2*c.inputs.s0*ratCoverDen c.inputs.xh/(ratCoverH c.inputs.xh*ratCoverW c.inputs.xh) ∧
  c.zlo ≤ 2*(43/10)^3*c.inputs.Plo*ratCoverH c.inputs.xl*c.inputs.s0/
    (ratCoverW c.inputs.xh*ratCoverDen c.inputs.xl) ∧
  c.Dlo ≤ (43/10)^3*c.inputs.Plo*(ratCoverH c.inputs.xl)^2/(ratCoverDen c.inputs.xl)^2 ∧
  c.Wlo ≤ 2*(43/10)^3*c.inputs.Plo^2*ratCoverH c.inputs.xl*c.inputs.s0/ratCoverDen c.inputs.xl ∧
  c.qmark+1/c.Rlo ≤ c.M ∧ c.M < c.zlo ∧
  c.ps ≤ (c.zlo-c.M)/(c.zlo-c.inputs.pl*c.M) ∧ c.inputs.Pu*ratCoverW c.inputs.xh ≤ c.pmax

instance instDecidableRatMarkedGeometryValid (c : RatMarkedGeometry) : Decidable c.Valid := by
  unfold RatMarkedGeometry.Valid
  infer_instance

noncomputable section

def RatMarkedGeometry.Sound (c : RatMarkedGeometry) : Prop :=
  ∀ {x s : ℝ} {n N : ℕ}, 0 < x → (c.inputs.xl:ℝ) ≤ x → x ≤ (c.inputs.xh:ℝ) →
    (c.inputs.s0:ℝ) ≤ s → (n:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3 →
    N=⌊coverSampleP x*(n:ℝ)⌋₊ →
    let p := (N:ℝ)/n
    let P := p/coverScaleW x
    let R := coverScaleR x s
    let z := coverScaleZ x s P
    let t := ⌈(c.qmark:ℝ)*R⌉₊
    (c.Rlo:ℝ) ≤ R ∧ (c.zlo:ℝ) ≤ z ∧ (c.Dlo:ℝ) ≤ coverScaleD x P ∧
    (c.Wlo:ℝ) ≤ coverScaleWgt x s P ∧ N ≤ n ∧ 2*N ≤ n ∧
    (c.inputs.pl:ℝ) ≤ p ∧ p ≤ (c.pmax:ℝ) ∧ 0 < p ∧ p < 1/2 ∧
    t < N ∧ (c.qmark:ℝ) ≤ (t:ℝ)/R ∧ (t:ℝ)/R ≤ (c.M:ℝ) ∧
    (c.dm:ℝ)*(c.qmark:ℝ) ≤ ((t:ℝ)/N)*((c.dm:ℝ)*z) ∧
    (c.ps:ℝ) ≤ (((N-t:ℕ):ℝ)/(n-t:ℕ))/p ∧
    0 < ((N-t:ℕ):ℝ)/(n-t:ℕ) ∧ ((N-t:ℕ):ℝ)/(n-t:ℕ) ≤ 1/2

theorem rat_marked_geometry_sound (c : RatMarkedGeometry) (hi : c.inputs.Valid)
    (hc : c.Valid) : c.Sound := by
  obtain ⟨hR,hz,hD,hW,hq,hdm,hpl,hps,hRb,hzb,hDb,hWb,hM,hMz,hpsb,hpmax⟩ := hc
  have hb := (rat_moment_certificate_valid c.inputs hi).sampling
  have hRbR : (c.Rlo:ℝ) ≤ 2*(c.inputs.s0:ℝ)*coverScaleDen (c.inputs.xh:ℝ)/
      (coverScaleH (c.inputs.xh:ℝ)*coverScaleW (c.inputs.xh:ℝ)) := by
    simpa only [rat_cover_den_cast,rat_cover_h_cast,rat_cover_w_cast,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr hRb
  have hzbR : (c.zlo:ℝ) ≤ 2*(43/10:ℝ)^3*(c.inputs.Plo:ℝ)*coverScaleH (c.inputs.xl:ℝ)*(c.inputs.s0:ℝ)/
      (coverScaleW (c.inputs.xh:ℝ)*coverScaleDen (c.inputs.xl:ℝ)) := by
    simpa only [rat_cover_den_cast,rat_cover_h_cast,rat_cover_w_cast,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr hzb
  have hDbR : (c.Dlo:ℝ) ≤ (43/10:ℝ)^3*(c.inputs.Plo:ℝ)*(coverScaleH (c.inputs.xl:ℝ))^2/
      (coverScaleDen (c.inputs.xl:ℝ))^2 := by
    simpa only [rat_cover_den_cast,rat_cover_h_cast,rat_cover_w_cast,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr hDb
  have hWbR : (c.Wlo:ℝ) ≤ 2*(43/10:ℝ)^3*(c.inputs.Plo:ℝ)^2*coverScaleH (c.inputs.xl:ℝ)*(c.inputs.s0:ℝ)/
      coverScaleDen (c.inputs.xl:ℝ) := by
    simpa only [rat_cover_den_cast,rat_cover_h_cast,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr hWb
  intro x s n N hx hxl hxh hs hn hN
  let p : ℝ := (N:ℝ)/n
  let P : ℝ := p/coverScaleW x
  obtain ⟨hnlo,hNlo,hPl,hPu,hplow,hpactual,hppos,hphalf⟩ :=
    cover_sampling_box_realizes c.inputs.realCertificate.box hb hx hxl hxh hs hn hN (p:=p) rfl (P:=P) rfl
  have hsmin : (1:ℝ) ≤ (c.inputs.s0:ℝ) := hb.density_lower
  have hs0 : (0:ℝ) < (c.inputs.s0:ℝ) := by linarith only [hsmin]
  obtain ⟨hRlower,hzlower,hDlower,hWlower⟩ := cover_scale_interval_lower hb.xl_nonneg hxl hx hxh
    hb.xmax hs0 hs hb.ratio_positive.le hPl
  have hRactual := hRbR.trans hRlower
  have hzactual := hzbR.trans hzlower
  have hDactual := hDbR.trans hDlower
  have hWactual := hWbR.trans hWlower
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith only [hb.order_four,hnlo]
  have hNhalf : 2*N ≤ n := by
    have hh : (N:ℝ) ≤ (1/2:ℝ)*n := (div_le_iff₀ hnpos).mp hphalf.le
    have hhh : (2:ℝ)*(N:ℝ) ≤ n := by linarith only [hh]
    exact_mod_cast hhh
  have hNn : N ≤ n := by omega
  have hpupper : p ≤ (c.pmax:ℝ) := by
    have hwpos := cover_w_pos hx
    have hEq : P*coverScaleW x=p := by dsimp only [P]; field_simp
    have hh : P*coverScaleW x ≤ (c.inputs.Pu:ℝ)*coverScaleW (c.inputs.xh:ℝ) :=
      mul_le_mul hPu (cover_w_mono hx.le hxh) (cover_w_nonneg x)
        (hb.ratio_positive.le.trans (hPl.trans hPu))
    rw [hEq] at hh
    apply hh.trans
    simpa only [rat_cover_w_cast,Rat.cast_mul] using (Rat.cast_le (K:=ℝ)).mpr hpmax
  have hNZ := cover_sample_order_eq_scale hnpos hx (hxh.trans hb.xmax) (hs0.trans_le hs) hn (p:=p) rfl (P:=P) rfl
  have hmark := cover_rounded_mark_parameters n N hNn hNhalf (q:=(c.qmark:ℝ))
    (M:=(c.M:ℝ)) (pl:=(c.inputs.pl:ℝ)) (ps:=(c.ps:ℝ)) (dm:=(c.dm:ℝ)) (by exact_mod_cast hq)
    (by exact_mod_cast hR) hRactual (by exact_mod_cast hM) (by exact_mod_cast hMz) hzactual hNZ
    (by exact_mod_cast hpl) hplow (by exact_mod_cast hpsb) (by exact_mod_cast hdm)
  exact ⟨hRactual,hzactual,hDactual,hWactual,hNn,hNhalf,hplow,hpupper,hppos,hphalf,hmark⟩

end
end Cycle12
