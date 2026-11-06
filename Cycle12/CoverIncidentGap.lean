import Cycle12.SamplerHalfRange

namespace Cycle12
noncomputable section

def coverIncidentGap (v : ℝ) : ℝ :=
  1/100+1001/40000*v-311/10000*v^2+407/5000*v^3+77/5000*v^4+49/10000*v^5

theorem cover_incident_gap_identity (v : ℝ) :
    1-2*(99/200+11/100*v+7/100*v^2)+v*(99/200+11/100*v+7/100*v^2)^2=
      coverIncidentGap v := by
  unfold coverIncidentGap
  ring

theorem cover_incident_gap_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    coverIncidentGap u ≤ coverIncidentGap v := by
  have hcoef : 0 ≤ (1001/40000:ℝ)-311/10000*(u+v)+407/5000*(u^2+u*v+v^2) := by
    nlinarith [sq_nonneg (u-v),sq_nonneg (u+v-311/1221)]
  have hbase := mul_nonneg (sub_nonneg.mpr huv) hcoef
  have hfour := pow_le_pow_left₀ hu huv 4
  have hfive := pow_le_pow_left₀ hu huv 5
  unfold coverIncidentGap
  nlinarith only [hbase,hfour,hfive]

theorem cover_incident_gap_positive {v : ℝ} (hv : 0 ≤ v) : (1/100:ℝ) ≤ coverIncidentGap v := by
  have hh := cover_incident_gap_mono (u:=0) (by norm_num) hv
  norm_num [coverIncidentGap] at hh ⊢
  exact hh

end
end Cycle12
