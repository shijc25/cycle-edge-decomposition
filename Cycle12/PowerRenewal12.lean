import Cycle12.PowerDecay12

namespace Cycle12
open Real Set
noncomputable section

theorem geometric_argument_lower {b x : ℝ} (hb : 0<b) (hb1 : b≤1) (hx : 0≤x) (j : ℕ) :
    x≤x/b^j := by
  apply (le_div_iff₀ (pow_pos hb _)).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (n:=j) hb.le hb1) hx

theorem PowerDecay.envelope {H : ℝ → ℝ} {w z x : ℝ} (hd : PowerDecay H w z) (hx : w≤x) :
    H x≤((2:ℝ)^(z*w)*H w)*(2:ℝ)^(-z*x) := by
  apply (hd (x:=w) le_rfl hx).trans_eq
  calc
    _ = (2:ℝ)^(z*w+-z*x)*H w := by congr 2; ring
    _ = _ := by rw [rpow_add (by norm_num : (0:ℝ)<2)]; ring

theorem PowerDecay.scaled_summable {H : ℝ → ℝ} {w z b x : ℝ}
    (hd : PowerDecay H w z) (h0 : ∀ y,w≤y → 0≤H y)
    (hw : 0<w) (hz : 0<z) (hb : 0<b) (hb1 : b<1) (hx : w≤x) :
    Summable (fun j : ℕ => H (x/b^j)) := by
  have hx0 := hw.trans_le hx
  have hj (j : ℕ) : w≤x/b^j := hx.trans (geometric_argument_lower hb hb1.le hx0.le j)
  have hh := (Cycle13.powerScaleSeries_summable (mul_pos hz hx0) hb hb1).mul_left
    ((2:ℝ)^(z*w)*H w)
  apply Summable.of_nonneg_of_le (fun j => h0 _ (hj j)) (fun j => ?_) hh
  have he : (2:ℝ)^(-z*(x/b^j))=Cycle13.powerScaleTerm (z*x) b j := by
    unfold Cycle13.powerScaleTerm
    congr 1
    simp only [div_eq_mul_inv,inv_pow]
    ring
  simpa only [he] using hd.envelope (hj j)

theorem PowerDecay.renewal_summable {H : ℝ → ℝ} {w z b x : ℝ}
    (hd : PowerDecay H w z) (h0 : ∀ y,w≤y → 0≤H y)
    (hw : 0<w) (hz : 0<z) (hb : 0<b) (hb1 : b<1) (hx : b*w≤x) :
    Summable (fun j : ℕ => H (x/b^(j+1))) := by
  have hx' : w≤x/b := (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hx)
  have hh := hd.scaled_summable h0 hw hz hb hb1 hx'
  convert hh using 1
  funext j
  congr 1
  rw [pow_succ]
  field_simp

/-- The first renewal argument is x/b, so the inherited decay rate is
z/b. This pays the infinite pair of terminal tails after the finite checks. -/
theorem PowerDecay.renewal_decay {H : ℝ → ℝ} {w z b : ℝ}
    (hd : PowerDecay H w z) (h0 : ∀ y,w≤y → 0≤H y)
    (hw : 0<w) (hz : 0<z) (hb : 0<b) (hb1 : b<1) :
    PowerDecay (renewalLoss H b) (b*w) (z/b) := by
  intro x y hx hxy
  have hy := hx.trans hxy
  have hsx := hd.renewal_summable h0 hw hz hb hb1 hx
  have hsy := hd.renewal_summable h0 hw hz hb hb1 hy
  unfold renewalLoss
  rw [←tsum_mul_left]
  apply Summable.tsum_le_tsum (fun j => ?_) hsy (hsx.mul_left _)
  have hargx := renewal_argument_mem hb hb1.le hw.le hx j
  have hargxy := div_le_div_of_nonneg_right hxy (pow_nonneg hb.le (j+1))
  have hh := hd hargx hargxy
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (h0 _ hargx)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hp : b^(j+1)≤b := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ (n:=j) hb.le hb1.le) hb.le
  have hdiv := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (pow_pos hb (j+1)) hp
  have hm := mul_le_mul_of_nonneg_left hdiv hz.le
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm]

theorem PowerDecay.series_half_tail {H : ℝ → ℝ} {w z b x : ℝ}
    (hd : PowerDecay H w z) (h0 : ∀ y,w≤y → 0≤H y)
    (hw : 0<w) (hz : 0<z) (hb : 0<b) (hb1 : b<1) (hx : w≤x)
    (N : ℕ) (hstep : 1≤z*(x/b^N)*(b⁻¹-1)) :
    (∑' j : ℕ,H (x/b^j))≤(∑ j∈Finset.range N,H (x/b^j))+2*H (x/b^N) := by
  have hs := hd.scaled_summable h0 hw hz hb hb1 hx
  have hx0 := hw.trans_le hx
  have hratio : ∀ j,N≤j → H (x/b^(j+1))≤(1/2:ℝ)*H (x/b^j) := by
    intro j hj
    have hjx := geometric_argument_lower hb hb1.le hx0.le j
    have hp : b^j≤b^N := pow_le_pow_of_le_one hb.le hb1.le hj
    have hnx := div_le_div_of_nonneg_left hx0.le (pow_pos hb j) hp
    have hdiff : x/b^(j+1)-x/b^j=(x/b^j)*(b⁻¹-1) := by rw [pow_succ]; field_simp <;> ring
    have hbInv : 0≤b⁻¹-1 := sub_nonneg.mpr ((one_le_inv₀ hb).mpr hb1.le)
    have hxy : x/b^j≤x/b^(j+1) := by
      have hh := mul_nonneg (div_nonneg hx0.le (pow_nonneg hb.le j)) hbInv
      rw [←hdiff] at hh
      linarith only [hh]
    apply (hd (hx.trans hjx) hxy).trans
    apply mul_le_mul_of_nonneg_right _ (h0 _ (hx.trans hjx))
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnx hbInv) hz.le
    have he : (2:ℝ)^(-z*(x/b^(j+1)-x/b^j))≤(2:ℝ)^(-1:ℝ) := by
      apply rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hdiff]
      nlinarith only [hstep,hh]
    simpa only [rpow_neg_one,one_div] using he
  have hh := Cycle13.geometric_remainder_bound hs.hasSum N
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1) hratio
  convert hh using 1 <;> ring

end
end Cycle12
