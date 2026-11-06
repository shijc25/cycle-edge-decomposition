import Cycle12.CoverBudgetPayments
import Cycle12.CoverCutProfile

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section

theorem cover_cube_budget_ratio {n m : ℝ} (hn : 0 ≤ n) (hm : 0 < m) :
    (43/10)*n*cubeScale m/m=coverScaleW (coverGraphX n m) := by
  rw [cover_graph_w_identity hn hm]
  have ht := cubeScale_pos hm
  have hc := cubeScale_cube hm.le
  generalize htdef : cubeScale m=t at *
  rw [← hc]
  field_simp

theorem cover_square_budget_ratio {n m : ℝ} (hm : 0 < m) :
    3*n*sqrt n=3*coverGraphX n m*((43/10)*n*cubeScale m) := by
  have ht := cubeScale_pos hm
  unfold coverGraphX
  field_simp

theorem cover_delete_threshold_eq_mu_expansion {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    coverDeleteThreshold n m=coverScaleMu (coverGraphX n m)*coverGraphExpansion n m := by
  have ht := cubeScale_pos hm
  have hH := cover_h_pos (cover_graph_x_pos hn hm).le
  have hd : (33/125:ℝ)*((43/10)*n*cubeScale m)/m=(33/125)*coverScaleW (coverGraphX n m) := by
    rw [← cover_cube_budget_ratio hn.le hm]
    ring
  unfold coverDeleteThreshold coverGraphExpansion coverScaleMu
  rw [hd]
  unfold coverScaleDen
  field_simp
  unfold coverGraphX
  field_simp
  <;> ring

theorem cover_cut_threshold_eq_strength {n m y : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hxmax : coverGraphX n m ≤ 17/250) (hy : 0 < y) :
    coverCutThreshold n m y=
      coverGraphExpansion n m*n*y*coverCutStrength (coverGraphX n m) y := by
  have hx := cover_graph_x_pos hn hm
  have hH := cover_h_pos hx.le
  have hd := cover_den_pos hx.le hxmax
  have hf : ((43/10)*n*cubeScale m)*cutShapeU y/(3*m)=
      cutShapeU y*coverScaleW (coverGraphX n m)/3 := by
    rw [← cover_cube_budget_ratio hn.le hm]
    ring
  unfold coverCutThreshold
  rw [hf,cover_square_budget_ratio hm]
  unfold coverGraphExpansion coverCutStrength coverProfileValue
  field_simp
  <;> ring

theorem cover_profile_cut_threshold_lower (C : CoverCutProfileCertificate) {n m y : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hxl : C.xl ≤ coverGraphX n m) (hxh : coverGraphX n m ≤ C.xh)
    (hy : 0 < y) (hyC : y ≤ C.side) :
    C.alpha*coverGraphExpansion n m*(y*n) ≤ coverCutThreshold n m y := by
  have hx := cover_graph_x_pos hn hm
  have hmax := hxh.trans C.xmax
  have hH := cover_h_pos hx.le
  have hd := cover_den_pos hx.le hmax
  have ht := cubeScale_pos hm
  have he : 0 ≤ coverGraphExpansion n m*n*y := by unfold coverGraphExpansion; positivity
  have hh := mul_le_mul_of_nonneg_left (cover_cut_profile_certificate_bound C hxl hxh hy hyC) he
  rw [cover_cut_threshold_eq_strength hn hm hmax hy]
  nlinarith only [hh]

theorem cover_graph_z_eq_sampling_expansion {n m p : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hxmax : coverGraphX n m ≤ 17/250) :
    coverScaleZ (coverGraphX n m) (sOf n m) (p/coverScaleW (coverGraphX n m))=
      p*coverGraphExpansion n m := by
  have hx := cover_graph_x_pos hn hm
  have hs : 0 < sOf n m := by unfold sOf; positivity
  have hH := cover_h_pos hx.le
  have hw := cover_w_pos hx
  have hd := cover_den_pos hx.le hxmax
  have hR : 0 < coverScaleR (coverGraphX n m) (sOf n m) := by unfold coverScaleR; positivity
  have hz := (cover_scale_relations (P:=p/coverScaleW (coverGraphX n m)) hx hxmax hs
    (cover_graph_coordinates_exact hn hm).1).2.2
  have hex := cover_graph_expansion_scale hn hm hxmax
  have hew : coverScaleW (coverGraphX n m)*(p/coverScaleW (coverGraphX n m))=p := by field_simp
  rw [hew] at hz
  apply (mul_left_cancel₀ hR.ne')
  calc
    _ = p*n := hz
    _ = _ := by nlinarith only [congrArg (fun t : ℝ => p*t) hex]

theorem cover_delete_threshold_gives_sample_mean {n m p degree : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hp : 0 ≤ p) (hxmax : coverGraphX n m ≤ 17/250)
    (hdegree : coverDeleteThreshold n m ≤ degree) :
    coverScaleMu (coverGraphX n m)*
      coverScaleZ (coverGraphX n m) (sOf n m) (p/coverScaleW (coverGraphX n m)) ≤ p*degree := by
  have hh := mul_le_mul_of_nonneg_left hdegree hp
  rw [cover_delete_threshold_eq_mu_expansion hn hm] at hh
  rw [cover_graph_z_eq_sampling_expansion hn hm hxmax]
  nlinarith only [hh]

end
end Cycle12
