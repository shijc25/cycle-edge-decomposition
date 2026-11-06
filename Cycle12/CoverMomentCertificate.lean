import Cycle12.CoverSampleRealization
import Cycle12.FixedNormalizedEdgeTails

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

structure CoverMomentCertificate where
  box : CoverSamplingBox
  density : ℝ
  edgeVariance : ℝ
  incidentVariance : ℝ
  edgeGap : ℝ
  incidentGap : ℝ

structure CoverMomentCertificate.Valid (c : CoverMomentCertificate) : Prop where
  sampling : c.box.Valid
  density : (if c.box.s0 ≤ 2 then 1/4 else (c.box.s0-1)/c.box.s0^2) ≤ c.density
  internal_variance :
    (1-c.box.pl)*(coverScaleW c.box.xh)^2*c.density*finiteOrderVarianceFactor c.box.nlo/
      (2*(43/10)^3*c.box.Plo) ≤ c.edgeVariance
  incident_variance :
    c.box.Pu*(coverScaleW c.box.xh)^2*(1-c.box.pl)^3*c.density*finiteOrderVarianceFactor c.box.nlo/
      (2*(43/10)^3) ≤ c.incidentVariance
  internal_gap : c.edgeGap ≤ 3/100-1/(c.box.Nlo*(1-1/c.box.nlo))
  incident_gap : c.incidentGap ≤
    (1+3*c.box.xl)*coverIncidentGap (coverSampleV c.box.xl)-c.box.Pu/(c.box.nlo-1)
  internal_positive : 0 < c.edgeGap
  incident_positive : 0 < c.incidentGap

/-- The certificate bounds the two actual fixed-size graph edge events.
It includes the floor operation and every continuous x and density in its box. -/
theorem cover_moment_certificate_sound (c : CoverMomentCertificate) (hc : c.Valid)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {x s : ℝ} {k : ℕ} (hm : 0 < (Fintype.card G.edgeSet:ℝ))
    (hx : 0 < x) (hxl : c.box.xl ≤ x) (hxh : x ≤ c.box.xh) (hs : c.box.s0 ≤ s)
    (hn : (Fintype.card V:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3)
    (hm_eq : (Fintype.card G.edgeSet:ℝ)=(Fintype.card V:ℝ)^2/(2*s))
    (hk : k=⌊coverSampleP x*(Fintype.card V:ℝ)⌋₊) :
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤
        (97/100)*((k:ℝ)/(Fintype.card V:ℝ))^2*(Fintype.card G.edgeSet:ℝ)) ≤
      c.edgeVariance/(c.edgeVariance+c.edgeGap^2) ∧
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => coverSampleV x*(Fintype.card G.edgeSet:ℝ) ≤ (incidentEdgeCount G S:ℝ)) ≤
      c.incidentVariance/(c.incidentVariance+c.incidentGap^2) := by
  let p : ℝ := (k:ℝ)/(Fintype.card V:ℝ)
  let P : ℝ := p/coverScaleW x
  have hs1 : 1 ≤ s := hc.sampling.density_lower.trans hs
  have hs0 : 0 < s := by linarith only [hs1]
  have hslo : 0 < c.box.s0 := by linarith only [hc.sampling.density_lower]
  have hw := cover_w_pos hx
  obtain ⟨hnlo,hNlo,hPl,hPu,hpl,hpsample,hp0,hphalf⟩ :=
    cover_sampling_box_realizes c.box hc.sampling hx hxl hxh hs hn hk (p:=p) rfl (P:=P) rfl
  have hn4R : (4:ℝ) ≤ Fintype.card V := hc.sampling.order_four.trans hnlo
  have hn4 : 4 ≤ Fintype.card V := by exact_mod_cast hn4R
  have hn0 : (0:ℝ) < Fintype.card V := by linarith only [hn4R]
  have hk1R : (1:ℝ) ≤ k := hc.sampling.sample_one.trans hNlo
  have hk1 : 1 ≤ k := by exact_mod_cast hk1R
  have hp1 : p ≤ 1 := hphalf.le.trans (by norm_num)
  have hklt : k < Fintype.card V := by
    have hh : (k:ℝ) < Fintype.card V := (div_lt_one hn0).mp (hphalf.trans (by norm_num))
    exact_mod_cast hh
  have hnlo2 : 2 < c.box.nlo := by linarith only [hc.sampling.order_four]
  have hN0 : 0 < c.box.Nlo := by linarith only [hc.sampling.sample_one]
  have hden := (cover_density_variance_box hslo hs).trans hc.density
  have hpeq : p=coverScaleW x*P := by dsimp [P]; field_simp
  have hve := (cover_internal_variance_box hnlo2 hnlo hw (cover_w_mono hx.le hxh)
    hs1 hc.sampling.ratio_positive hPl hpl hp1 hden hn hpeq).trans hc.internal_variance
  have hvi := (cover_incident_variance_box hnlo2 hnlo hw (cover_w_mono hx.le hxh)
    hs1 (hc.sampling.ratio_positive.le.trans hPl) hPu hpl hp1 hden hn hpeq).trans hc.incident_variance
  constructor
  · apply fixed_internal_edge_tail_budget G hn4 hk1 hklt.le hm hs0 (p:=p) rfl hm_eq
      (show 1 < c.box.nlo by linarith only [hnlo2]) hnlo hN0 hNlo hve hc.internal_positive
    convert hc.internal_gap using 1 <;> norm_num
  · apply fixed_incident_edge_tail_budget G hn4 hklt hm hs0 hw (p:=p) rfl hm_eq hvi hc.incident_positive
    have hg := cover_incident_gap_box (Fintype.card V) k hc.sampling.xl_nonneg hxl hx
      (hxh.trans hc.sampling.xmax) (by linarith only [hnlo2]) hnlo hklt.le hpsample
      ((cover_p0_mono hx.le hxh).trans hc.sampling.ratio_upper)
    exact (mul_le_mul_of_nonneg_right hc.incident_gap hw.le).trans hg

end
end Cycle12
