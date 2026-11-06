import Cycle12.RationalCutBin
import Cycle12.RationalIntervalCover

namespace Cycle12

structure RatCutRegion where
  bin : RatCutBinCertificate
  upper : Option ℚ
  cap : ℚ
  Rlo : ℚ

def RatCutRegion.interval (c : RatCutRegion) : RatSideInterval :=
  ⟨c.bin.residual.retention.nu,c.upper⟩

def RatCutRegion.Valid (c : RatCutRegion) : Prop :=
  0 < c.Rlo ∧ match c.upper with
  | none => c.cap ≤ c.bin.residual.retention.ymax
  | some r => 0 ≤ r ∧ min c.cap (r/c.Rlo) ≤ c.bin.residual.retention.ymax

instance instDecidableRatCutRegionValid (c : RatCutRegion) : Decidable c.Valid := by
  unfold RatCutRegion.Valid
  cases c.upper <;> infer_instance

noncomputable section

theorem rat_cut_region_side_bounds (c : RatCutRegion) (hc : c.Valid)
    {n h R u : ℝ} (hh : 0 < h) (hR : (c.Rlo:ℝ) ≤ R) (hn : n=R*h)
    (hside : c.interval.Contains (u/h)) (hcap : u ≤ (c.cap:ℝ)*n) :
    (c.bin.residual.retention.nu:ℝ)*h ≤ u ∧ u ≤ (c.bin.residual.retention.ymax:ℝ)*n := by
  have hRl : (0:ℝ) < (c.Rlo:ℝ) := by exact_mod_cast hc.1
  have hnp : 0 < n := by rw [hn]; exact mul_pos (hRl.trans_le hR) hh
  refine ⟨(le_div_iff₀ hh).mp hside.1,?_⟩
  cases he : c.upper with
  | none =>
    have hb : c.cap ≤ c.bin.residual.retention.ymax := by simpa only [he] using hc.2
    exact hcap.trans (mul_le_mul_of_nonneg_right ((Rat.cast_le (K:=ℝ)).mpr hb) hnp.le)
  | some r =>
    have hb : 0 ≤ r ∧ min c.cap (r/c.Rlo) ≤ c.bin.residual.retention.ymax := by
      simpa only [he] using hc.2
    have hr : (0:ℝ) ≤ (r:ℝ) := by exact_mod_cast hb.1
    have hu : u ≤ (r:ℝ)*h := (div_le_iff₀ hh).mp (hside.2 r he)
    have hRu : (r:ℝ)*h ≤ ((r:ℝ)/(c.Rlo:ℝ))*n := by
      rw [hn]
      have hm := mul_le_mul_of_nonneg_left hR (div_nonneg hr hRl.le)
      have hid : ((r:ℝ)/(c.Rlo:ℝ))*(c.Rlo:ℝ)=(r:ℝ) := by field_simp
      rw [hid] at hm
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm hh.le
    have hmin : u ≤ min (c.cap:ℝ) ((r:ℝ)/(c.Rlo:ℝ))*n := by
      rw [min_mul_of_nonneg _ _ hnp.le]
      exact le_min hcap (hu.trans hRu)
    have hbR := (Rat.cast_le (K:=ℝ)).mpr hb.2
    push_cast at hbR
    exact hmin.trans (mul_le_mul_of_nonneg_right hbR hnp.le)

theorem rat_cut_region_ray_cover (cs : List RatCutRegion) {lo : ℚ}
    (hc : ratRayChain lo (cs.map RatCutRegion.interval)) {x : ℝ} (hx : (lo:ℝ) ≤ x) :
    ∃ c∈cs, c.interval.Contains x := by
  obtain ⟨a,ha,hax⟩ := rat_ray_chain_covers hc hx
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  exact ⟨c,hc,hax⟩

theorem rat_cut_region_closed_cover (cs : List RatCutRegion) {lo hi : ℚ}
    (hc : ratClosedChain hi lo (cs.map RatCutRegion.interval)) {x : ℝ}
    (hlo : (lo:ℝ) ≤ x) (hhi : x ≤ (hi:ℝ)) :
    ∃ c∈cs, c.interval.Contains x := by
  obtain ⟨a,ha,hax⟩ := rat_closed_chain_covers hc hlo hhi
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  exact ⟨c,hc,hax⟩

end
end Cycle12
