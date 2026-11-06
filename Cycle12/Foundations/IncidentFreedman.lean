import Cycle12.Foundations.MonotoneBernoulliTail
import Cycle12.Foundations.IncidentSampleEdges

/-! The exact incident-edge Freedman budget used by the coefficient-13
certificates, proved by finite Bernoulli exposure. -/
namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem incidentEdgeCount_freedman (G : SimpleGraph V) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1) {r t : ℝ} (hr : 0 < r)
    (hm : 0 < (Fintype.card G.edgeSet:ℝ)) (ht : 0 < t)
    (hdeg : ∀ v, (G.degree v:ℝ) ≤ r) :
    (bernoulliSubset p).prob (fun S =>
      (2*(p:ℝ)-(p:ℝ)^2)*(Fintype.card G.edgeSet:ℝ)+t ≤ (incidentEdgeCount G S:ℝ)) ≤
    exp (-t^2/(2*(2*(p:ℝ)*(1-(p:ℝ))*(Fintype.card G.edgeSet:ℝ)*r+
      (1-(p:ℝ))*r*t/3))) := by
  have hv : 0 < 2*(p:ℝ)*(1-(p:ℝ))*(Fintype.card G.edgeSet:ℝ)*r :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hp0) (sub_pos.mpr hp1)) hm) hr
  have hvar : (p:ℝ)*(1-(p:ℝ))*(∑ v : V, (G.degree v:ℝ)^2) ≤
      2*(p:ℝ)*(1-(p:ℝ))*(Fintype.card G.edgeSet:ℝ)*r := by
    have hh := mul_le_mul_of_nonneg_left (degree_square_sum_le G hdeg)
      (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2))
    nlinarith
  have hh := subsetBernoulli_monotone_upper_tail (univ:Finset V) p
    (fun S => (incidentEdgeCount G S:ℝ)) (fun v => (G.degree v:ℝ)) hr.le hv ht
    (fun v _ => ⟨Nat.cast_nonneg _,hdeg v⟩)
    (fun v _ S _ => incidentEdgeCount_increment G S v) hvar
  simpa only [subsetBernoulli_univ,incidentEdgeCount_expect] using hh

theorem incidentEdgeCount_freedman_fraction (G : SimpleGraph V) (p : unitInterval)
    (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1) {r v : ℝ} (hr : 0 < r)
    (hm : 0 < (Fintype.card G.edgeSet:ℝ)) (hv : 2*(p:ℝ)-(p:ℝ)^2 < v)
    (hdeg : ∀ x, (G.degree x:ℝ) ≤ r) :
    (bernoulliSubset p).prob (fun S =>
      v*(Fintype.card G.edgeSet:ℝ) ≤ (incidentEdgeCount G S:ℝ)) ≤
    exp (-((Fintype.card G.edgeSet:ℝ)/r)*(v-2*(p:ℝ)+(p:ℝ)^2)^2/
      ((1-(p:ℝ))*(4*(p:ℝ)+2*(v-2*(p:ℝ)+(p:ℝ)^2)/3))) := by
  let m : ℝ := Fintype.card G.edgeSet
  let gap := v-2*(p:ℝ)+(p:ℝ)^2
  have hg : 0 < gap := by dsimp [gap]; linarith
  have hh := incidentEdgeCount_freedman G p hp0 hp1 hr hm (mul_pos hg hm) hdeg
  have he : (2*(p:ℝ)-(p:ℝ)^2)*m+gap*m=v*m := by dsimp [gap]; ring
  change (bernoulliSubset p).prob (fun S =>
    (2*(p:ℝ)-(p:ℝ)^2)*m+gap*m ≤ (incidentEdgeCount G S:ℝ)) ≤ _ at hh
  rw [he] at hh
  apply hh.trans_eq
  congr 1
  change -(gap*m)^2/(2*(2*(p:ℝ)*(1-(p:ℝ))*m*r+(1-(p:ℝ))*r*(gap*m)/3))=
    -(m/r)*gap^2/((1-(p:ℝ))*(4*(p:ℝ)+2*gap/3))
  have hp : 0 < 1-(p:ℝ) := sub_pos.mpr hp1
  have hd : 0 < 4*(p:ℝ)+2*gap/3 := by positivity
  have hd' : 0 < 2*(p:ℝ)*(1-(p:ℝ))*m*r+(1-(p:ℝ))*r*(gap*m)/3 := by positivity
  have hd'' : 0 < 6*(p:ℝ)+gap := by positivity
  field_simp [hr.ne',hm.ne',hp.ne',hd.ne',hd'.ne',hd''.ne']
  <;> ring

end
end Cycle13
