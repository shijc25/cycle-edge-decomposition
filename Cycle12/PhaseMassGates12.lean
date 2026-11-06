import Cycle12.PhaseLayerMass12

namespace Cycle12.Global12
open Real
noncomputable section

/-- An upper bound on overlap certifies the reciprocal mass factor. -/
theorem mass_fraction_of_upper {Z z m : ℝ} (hZ : Z ≤ z) (hz : z < 1)
    (hm : 0 ≤ m) (hpay : 1 ≤ m*(1-z)) : Z < 1 ∧ 1/(1-Z) ≤ m := by
  have hZ1 := hZ.trans_lt hz
  refine ⟨hZ1,(div_le_iff₀ (sub_pos.mpr hZ1)).mpr ?_⟩
  exact hpay.trans (mul_le_mul_of_nonneg_left (by linarith only [hZ]) hm)

/-- Three certified scalar series bounds determine all phase mass factors. -/
theorem phase_mass_gates {A v e f m1 m2 m3 : ℝ}
    (hv : (2:ℝ)^(-delta*(theta1*theta2*A)) ≤ v)
    (he : scaleMassSeries theta2 (delta*(theta2*A)) ≤ e)
    (hf : scaleMassSeries theta2 (delta*A) ≤ f)
    (hz1 : overlap*(v+e) < 1) (hz2 : overlap*e < 1) (hz3 : overlap*f < 1)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hm3 : 0 ≤ m3)
    (hp1 : 1 ≤ m1*(1-overlap*(v+e)))
    (hp2 : 1 ≤ m2*(1-overlap*e)) (hp3 : 1 ≤ m3*(1-overlap*f)) :
    phaseOverlap1 A < 1 ∧ phaseMass1 A ≤ m1 ∧
    phaseOverlap2 A < 1 ∧ phaseMass2 A ≤ m2 ∧
    phaseOverlap3 A < 1 ∧ phaseMass3 A ≤ m3 := by
  have ho : 0 ≤ overlap := by norm_num [overlap]
  have h1 : phaseOverlap1 A ≤ overlap*(v+e) := mul_le_mul_of_nonneg_left (add_le_add hv he) ho
  have h2 : phaseOverlap2 A ≤ overlap*e := mul_le_mul_of_nonneg_left he ho
  have h3 : phaseOverlap3 A ≤ overlap*f := mul_le_mul_of_nonneg_left hf ho
  obtain ⟨hz1',hp1'⟩ := mass_fraction_of_upper h1 hz1 hm1 hp1
  obtain ⟨hz2',hp2'⟩ := mass_fraction_of_upper h2 hz2 hm2 hp2
  obtain ⟨hz3',hp3'⟩ := mass_fraction_of_upper h3 hz3 hm3 hp3
  exact ⟨hz1',hp1',hz2',hp2',hz3',hp3'⟩

end
end Cycle12.Global12
