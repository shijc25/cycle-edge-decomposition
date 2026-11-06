import Cycle12.CoverVarianceBudget
import Cycle12.FixedIncidentVariance

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem simple_graph_edge_mass_cap (G : SimpleGraph V) :
    2*(Fintype.card G.edgeSet:ℝ) ≤ (Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1) := by
  have hd (v : V) : (G.degree v:ℝ) ≤ (Fintype.card V:ℝ)-1 := by
    have hh : G.degree v+1 ≤ Fintype.card V := G.degree_lt_card_verts v
    have hhR : (G.degree v:ℝ)+1 ≤ (Fintype.card V:ℝ) := by exact_mod_cast hh
    linarith only [hhR]
  have hs := sum_le_sum (s:=univ) (fun v _ => hd v)
  have ht : (∑ v, (G.degree v:ℝ))=2*(Fintype.card G.edgeSet:ℝ) := by
    have hh := G.sum_degrees_eq_twice_card_edges
    rw [← G.card_edgeSet] at hh
    exact_mod_cast hh
  simpa only [ht,sum_const,card_univ,nsmul_eq_mul] using hs

theorem fixed_graph_internal_normalized_variance (G : SimpleGraph V)
    (hn : 4 ≤ Fintype.card V) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card V)
    {p s : ℝ} (hm : 0 < (Fintype.card G.edgeSet:ℝ)) (hs : 0 < s)
    (hp : p=(k:ℝ)/(Fintype.card V:ℝ))
    (hm_eq : (Fintype.card G.edgeSet:ℝ)=(Fintype.card V:ℝ)^2/(2*s)) :
    (fixedSizeLaw (univ:Finset V) k).expect
      (fun S => ((sampledFinsetEdgeCount G S:ℝ)-
        (Fintype.card G.edgeSet:ℝ)*fixedChooseRatio (Fintype.card V) k 2)^2) ≤
      (2*(1-p)*(s-1)/(p*(Fintype.card V:ℝ))*finiteOrderVarianceFactor (Fintype.card V))*
        (p^2*(Fintype.card G.edgeSet:ℝ))^2 := by
  have hnR : (2:ℝ) < Fintype.card V := by exact_mod_cast (show 2 < Fintype.card V by omega)
  have hn0 : (0:ℝ) < Fintype.card V := by linarith only [hnR]
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp0 : 0 < p := by rw [hp]; positivity
  have hkeq : (k:ℝ)=p*(Fintype.card V:ℝ) := by rw [hp]; field_simp
  exact (fixed_sample_edge_variance_bound G hn hk).trans
    (fixed_internal_variance_normalized hnR hm hp0 hs (by exact_mod_cast hk1)
      (by exact_mod_cast hk) (simple_graph_edge_mass_cap G) hkeq hm_eq)

theorem fixed_graph_incident_normalized_variance (G : SimpleGraph V)
    (hn : 4 ≤ Fintype.card V) {k : ℕ} (hk : k < Fintype.card V)
    {p s w : ℝ} (hm : 0 < (Fintype.card G.edgeSet:ℝ)) (hs : 0 < s) (hw : 0 < w)
    (hp : p=(k:ℝ)/(Fintype.card V:ℝ))
    (hm_eq : (Fintype.card G.edgeSet:ℝ)=(Fintype.card V:ℝ)^2/(2*s)) :
    (fixedSizeLaw (univ:Finset V) k).expect
      (fun S => ((incidentEdgeCount G S:ℝ)-(Fintype.card G.edgeSet:ℝ)*
        (1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2))^2) ≤
      (2*p*(1-p)^3*(s-1)/(w^2*(Fintype.card V:ℝ))*finiteOrderVarianceFactor (Fintype.card V))*
        (w*(Fintype.card G.edgeSet:ℝ))^2 := by
  have hnR : (2:ℝ) < Fintype.card V := by exact_mod_cast (show 2 < Fintype.card V by omega)
  have hn0 : (0:ℝ) < Fintype.card V := by linarith only [hnR]
  have hkeq : (k:ℝ)=p*(Fintype.card V:ℝ) := by rw [hp]; field_simp
  have hcomp : (1:ℝ) ≤ (Fintype.card V:ℝ)-(k:ℝ) := by
    have hh : (k:ℝ)+1 ≤ Fintype.card V := by exact_mod_cast hk
    linarith only [hh]
  have hh := fixed_incident_variance_normalized hnR hm hs hw (Nat.cast_nonneg k)
    hcomp (simple_graph_edge_mass_cap G) hkeq hm_eq
  rw [← Nat.cast_sub hk.le] at hh
  exact (fixed_sample_incident_variance_bound G hn hk.le).trans hh

end
end Cycle12
