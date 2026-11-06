import Cycle12.Foundations.MixedElementaryTails

namespace Cycle13.MixedSample
open Real Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

def cubeScale (m : ℝ) : ℝ := m^((3:ℝ)⁻¹)
def xOf (n m : ℝ) : ℝ := sqrt n/(6*cubeScale m)
def sOf (n m : ℝ) : ℝ := n^2/(2*m)

theorem cubeScale_pos {m : ℝ} (hm : 0 < m) : 0 < cubeScale m := rpow_pos_of_pos hm _

theorem cubeScale_cube {m : ℝ} (hm : 0 ≤ m) : (cubeScale m)^3=m := by
  exact rpow_inv_natCast_pow hm (by norm_num : (3:ℕ) ≠ 0)

theorem xOf_pos {n m : ℝ} (hn : 0 < n) (hm : 0 < m) : 0 < xOf n m :=
  div_pos (sqrt_pos.mpr hn) (mul_pos (by norm_num) (cubeScale_pos hm))

theorem w_xOf {n m : ℝ} (hn : 0 ≤ n) (hm : 0 < m) :
    w (xOf n m)=6*n/(cubeScale m)^2 := by
  have ht := (cubeScale_pos hm).ne'
  unfold w xOf
  rw [div_pow,sq_sqrt hn]
  field_simp <;> ring

theorem coordinate_algebra {n m t x : ℝ} (hn : 0 < n) (ht : 0 < t)
    (hm : t^3=m) (hw : w x=6*n/t^2) :
    (sOf n m)^2*order x=n ∧ edgeCount x (sOf n m)=m := by
  have ho : order x=4*m^2/n^3 := by
    unfold order
    rw [hw,← hm]
    field_simp <;> ring
  rw [ho]
  constructor
  · unfold sOf
    rw [← hm]
    field_simp <;> ring
  · unfold edgeCount
    rw [ho]
    unfold sOf
    rw [← hm]
    field_simp <;> ring

theorem xOf_sOf_coordinates {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    (sOf n m)^2*order (xOf n m)=n ∧ edgeCount (xOf n m) (sOf n m)=m :=
  coordinate_algebra hn (cubeScale_pos hm) (cubeScale_cube hm.le) (w_xOf hn.le hm)

theorem sOf_ge_one {n m : ℝ} (hm : 0 < m) (hsize : 2*m ≤ n^2) : 1 ≤ sOf n m := by
  unfold sOf
  exact (one_le_div (by positivity)).mpr hsize

variable {V : Type} [Fintype V] [DecidableEq V]

theorem twice_graph_edges_le_order_sq (G : SimpleGraph V) :
    2*(Fintype.card G.edgeSet:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
  have hdeg : ∀ v : V, G.degree v ≤ Fintype.card V := fun v => (G.degree_lt_card_verts v).le
  have hh : 2*G.edgeFinset.card ≤ (Fintype.card V)^2 := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc
      _ ≤ ∑ _v : V, Fintype.card V := sum_le_sum (fun v _ => hdeg v)
      _ = _ := by simp [pow_two]
  have he : G.edgeFinset.card=Fintype.card G.edgeSet := G.edgeFinset_card
  rw [he] at hh
  exact_mod_cast hh

/-- Every finite simple graph with at least one edge has the exact coordinates
used by the sampling certificates. The scale is automatically at least one. -/
theorem graph_coordinates (G : SimpleGraph V) (hm : 0 < Fintype.card G.edgeSet) :
    ∃ x s : ℝ, 0 < x ∧ 1 ≤ s ∧
      (Fintype.card V:ℝ)=s^2*order x ∧ (Fintype.card G.edgeSet:ℝ)=edgeCount x s := by
  have hmR : (0:ℝ) < Fintype.card G.edgeSet := by exact_mod_cast hm
  have hsize := twice_graph_edges_le_order_sq G
  have hnR : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  obtain ⟨hn,he⟩ := xOf_sOf_coordinates hnR hmR
  exact ⟨xOf (Fintype.card V) (Fintype.card G.edgeSet),
    sOf (Fintype.card V) (Fintype.card G.edgeSet),xOf_pos hnR hmR,
    sOf_ge_one hmR hsize,hn.symm,he.symm⟩

end
end Cycle13.MixedSample
