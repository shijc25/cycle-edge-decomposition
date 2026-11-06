import Cycle12.FixedSamplingGeometry
import Cycle12.CoverScaleEnvelopes

namespace Cycle12
noncomputable section

theorem residual_ratio_scale_mono {lower z pl M : ℝ}
    (hM0 : 0 ≤ M) (hMl : M < lower) (hlz : lower ≤ z)
    (hpl0 : 0 ≤ pl) (hpl1 : pl ≤ 1) :
    (lower-M)/(lower-pl*M) ≤ (z-M)/(z-pl*M) := by
  have hpM := mul_le_mul_of_nonneg_right hpl1 hM0
  have hd0 : 0 < lower-pl*M := by linarith only [hpM,hMl]
  have hd1 : 0 < z-pl*M := by linarith only [hpM,hMl,hlz]
  apply (div_le_div_iff₀ hd0 hd1).mpr
  have hh := mul_nonneg (mul_nonneg hM0 (sub_nonneg.mpr hpl1)) (sub_nonneg.mpr hlz)
  nlinarith only [hh]

theorem cover_sample_order_eq_scale {n p P x s : ℝ} {N : ℕ}
    (hn0 : 0 < n) (hx : 0 < x) (hxmax : x ≤ 17/250) (hs : 0 < s)
    (hn : n=4*(43/10)^3*s^2/(coverScaleW x)^3)
    (hp : p=(N:ℝ)/n) (hP : P=p/coverScaleW x) :
    (N:ℝ)=coverScaleZ x s P*coverScaleR x s := by
  have hw := cover_w_pos hx
  have hh := (cover_scale_relations (P:=P) hx hxmax hs hn).2.2
  have he : coverScaleW x*P*n=(N:ℝ) := by rw [hP,hp]; field_simp
  rw [he] at hh
  simpa only [mul_comm] using hh.symm

/-- All rounded marking facts used by the vote and residual-sampling
certificates, with a cap chosen from a lower bound on the true scale. -/
theorem cover_rounded_mark_parameters (n N : ℕ) (hN : N ≤ n) (hhalf : 2*N ≤ n)
    {q R Rlo z zlo M pl ps dm : ℝ} (hq : 0 ≤ q) (hRlo : 0 < Rlo) (hRl : Rlo ≤ R)
    (hM : q+1/Rlo ≤ M) (hMz : M < zlo) (hzlo : zlo ≤ z)
    (hNZ : (N:ℝ)=z*R) (hpl0 : 0 ≤ pl) (hpl : pl ≤ (N:ℝ)/n)
    (hps : ps ≤ (zlo-M)/(zlo-pl*M)) (hdm : 0 ≤ dm) :
    ⌈q*R⌉₊ < N ∧
    q ≤ (⌈q*R⌉₊:ℝ)/R ∧ (⌈q*R⌉₊:ℝ)/R ≤ M ∧
    dm*q ≤ ((⌈q*R⌉₊:ℝ)/N)*(dm*z) ∧
    ps ≤ (((N-⌈q*R⌉₊:ℕ):ℝ)/(n-⌈q*R⌉₊:ℕ))/((N:ℝ)/n) ∧
    0 < ((N-⌈q*R⌉₊:ℕ):ℝ)/(n-⌈q*R⌉₊:ℕ) ∧
    ((N-⌈q*R⌉₊:ℕ):ℝ)/(n-⌈q*R⌉₊:ℕ) ≤ 1/2 := by
  have hR := hRlo.trans_le hRl
  have hM0 : 0 ≤ M := (add_nonneg hq (one_div_pos.mpr hRlo).le).trans hM
  have hz : 0 < z := (hM0.trans_lt hMz).trans_le hzlo
  have hqcap : q+1/R ≤ M := (add_le_add le_rfl (one_div_le_one_div_of_le hRlo hRl)).trans hM
  have hzid : (N:ℝ)/R=z := by rw [hNZ]; field_simp
  have ht : ⌈q*R⌉₊ < N := rounded_marks_lt_sample hq hR N (by rw [hzid]; exact hqcap.trans_lt (hMz.trans_le hzlo))
  have htD : ⌈q*R⌉₊ < n := ht.trans_le hN
  have hn0 : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt htD)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have hmarks := rounded_mark_count_bounds hq hR
  have hcap := hmarks.2.trans hqcap
  have hp1 : (N:ℝ)/n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hN)
  have hpl1 := hpl.trans hp1
  have hmark0 : 0 ≤ (⌈q*R⌉₊:ℝ)/R := by positivity
  have hfrac := (residual_ratio_scale_mono hM0 hMz hzlo hpl0 hpl1).trans
    (residual_ratio_population_lower hz hpl0 hpl hp1 hmark0 hcap (hMz.trans_le hzlo))
  have hratio := residual_sampling_ratio_identity n N ⌈q*R⌉₊ hN ht hR
  rw [hzid] at hratio
  have hpsactual := hps.trans hfrac
  rw [← hratio] at hpsactual
  have hvote : dm*q ≤ ((⌈q*R⌉₊:ℝ)/N)*(dm*z) := by
    have hh := mul_le_mul_of_nonneg_left hmarks.1 hdm
    have he : dm*((⌈q*R⌉₊:ℝ)/R)=((⌈q*R⌉₊:ℝ)/N)*(dm*z) := by
      rw [hNZ]
      field_simp
    rwa [he] at hh
  have hresN : (0:ℝ) < (N-⌈q*R⌉₊:ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt ht)
  have hresD : (0:ℝ) < (n-⌈q*R⌉₊:ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt htD)
  refine ⟨ht,hmarks.1,hcap,hvote,hpsactual,div_pos hresN hresD,?_⟩
  apply (div_le_iff₀ hresD).mpr
  have hh := fixed_sampling_residual_half n N ⌈q*R⌉₊ ht.le hhalf
  have hhR : 2*((N-⌈q*R⌉₊:ℕ):ℝ) ≤ (n-⌈q*R⌉₊:ℕ) := by exact_mod_cast hh
  linarith only [hhR]

end
end Cycle12
