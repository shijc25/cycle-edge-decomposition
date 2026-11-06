import Cycle12.CoverRoutingCoordinates

namespace Cycle12
open Real
noncomputable section

def directOutsideCapacity (n N : ℕ) : ℕ := ⌈((n:ℝ)-(N:ℝ))/(N:ℝ)⌉₊

theorem direct_outside_capacity_bounds {n N : ℕ} (hN : 0 < N) (hn : 2*N ≤ n) :
    0 < directOutsideCapacity n N ∧ n-N ≤ directOutsideCapacity n N*N ∧
      (directOutsideCapacity n N:ℝ) ≤ (n:ℝ)/(N:ℝ) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : 2*(N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hNn : N ≤ n := by omega
  have hNnR : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hNn
  have ha : 1 ≤ ((n:ℝ)-(N:ℝ))/(N:ℝ) := (le_div_iff₀ hNR).mpr (by linarith only [hnR])
  have hnon : 0 ≤ ((n:ℝ)-(N:ℝ))/(N:ℝ) := by linarith only [ha]
  refine ⟨?_,?_,?_⟩
  · unfold directOutsideCapacity
    exact Nat.ceil_pos.mpr (by linarith only [ha])
  · have hh := (div_le_iff₀ hNR).mp (Nat.le_ceil (((n:ℝ)-(N:ℝ))/(N:ℝ)))
    have hc : ((n-N:ℕ):ℝ) ≤ (directOutsideCapacity n N*N:ℕ) := by
      simpa only [Nat.cast_sub hNn,Nat.cast_mul,directOutsideCapacity] using hh
    exact_mod_cast hc
  · have hh := Nat.ceil_lt_add_one hnon
    have he : ((n:ℝ)-(N:ℝ))/(N:ℝ)+1=(n:ℝ)/(N:ℝ)  := by field_simp; ring
    rw [he] at hh
    exact hh.le

def coverDirectCubic (b x s P : ℝ) : ℝ :=
  b^3*2*(43/10)^6*P^4*(coverScaleH x)^3*s*coverScaleW x/(coverScaleDen x)^3

theorem cover_direct_ratio {b x s P : ℝ} (hb : 0 < b) (hx : 0 < x)
    (hxm : x ≤ 17/250) (hs : 0 < s) (hP : 0 < P) :
    coverRoutingOrder x s P/(b*coverScaleZ x s P)=coverScaleR x s/b := by
  have hw := (cover_w_pos hx).ne'
  have hd := (cover_den_pos hx.le hxm).ne'
  have hH := (cover_h_pos hx.le).ne'
  unfold coverRoutingOrder coverScaleZ coverScaleR
  field_simp
  <;> ring

theorem cover_direct_cubic_identity {b x s P : ℝ} (hx : 0 < x) (hxm : x ≤ 17/250) :
    (b*coverScaleZ x s P)^3*(P*coverScaleW x)^2=
      coverDirectCubic b x s P*coverRoutingOrder x s P := by
  have hw := (cover_w_pos hx).ne'
  have hd := (cover_den_pos hx.le hxm).ne'
  unfold coverScaleZ coverDirectCubic coverRoutingOrder
  field_simp
  <;> ring

theorem cover_direct_cubic_lower {b xl x s0 s lower P : ℝ}
    (hb : 0 ≤ b) (hxl : 0 ≤ xl) (hxlx : xl ≤ x) (hxm : x ≤ 17/250)
    (hs0 : 0 ≤ s0) (hs : s0 ≤ s) (hlower : 0 ≤ lower) (hP : lower ≤ P) :
    coverDirectCubic b xl s0 lower ≤ coverDirectCubic b x s P := by
  have hd := cover_den_pos (hxl.trans hxlx) hxm
  have hw := cover_w_mono hxl hxlx
  have hh := cover_h_mono hxlx
  have hden := cover_den_antitone hxl hxlx
  have hH := cover_h_pos hxl
  have hwl := cover_w_nonneg xl
  have hspos := hs0.trans hs
  have hHpos := cover_h_pos (hxl.trans hxlx)
  have hwpos := cover_w_nonneg x
  unfold coverDirectCubic
  gcongr <;> positivity

theorem cover_direct_cubic_capacity {c b x s P : ℝ}
    (hc0 : 0 ≤ c) (hb : 0 < b) (hx : 0 < x) (hxm : x ≤ 17/250)
    (hs : 0 < s) (hP : 0 < P) (hc : c ≤ 1/(P*coverScaleW x))
    (hbound : 324 ≤ coverDirectCubic b x s P) :
    324*c^2*coverRoutingOrder x s P ≤ (b*coverScaleZ x s P)^3 := by
  have hp : 0 < P*coverScaleW x := mul_pos hP (cover_w_pos hx)
  have hcp : c*(P*coverScaleW x) ≤ 1 := (le_div_iff₀ hp).mp hc
  have hsq : c^2*(P*coverScaleW x)^2 ≤ 1 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hc0 hp.le) hcp 2
    simpa only [mul_pow,one_pow] using hh
  have hN := cover_routing_order_pos hx hs hP
  have hh := mul_le_mul_of_nonneg_right hbound hN.le
  have he := cover_direct_cubic_identity (b:=b) (s:=s) (P:=P) hx hxm
  have hh' := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 324*coverRoutingOrder x s P by positivity)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).mp
  nlinarith only [hh,he,hh']

end
end Cycle12
