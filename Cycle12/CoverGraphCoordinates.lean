import Cycle12.CoverScaleEnvelopes
import Cycle12.FixedGraphNormalizedVariance
import Cycle12.Foundations.MixedGraphCoordinates

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable

def coverGraphX (n m : ℝ) : ℝ := sqrt n/((43/10)*cubeScale m)
def coverGraphBudget (n m : ℝ) : ℝ := (43/10)*n*cubeScale m+3*n*sqrt n
def coverGraphExpansion (n m : ℝ) : ℝ :=
  (43/10)*cubeScale m*coverScaleH (coverGraphX n m)/coverScaleDen (coverGraphX n m)

theorem cover_graph_x_pos {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    0 < coverGraphX n m := by
  unfold coverGraphX
  exact div_pos (sqrt_pos.mpr hn) (mul_pos (by norm_num) (cubeScale_pos hm))

theorem cover_graph_w_identity {n m : ℝ} (hn : 0 ≤ n) (hm : 0 < m) :
    coverScaleW (coverGraphX n m)=(43/10)*n/(cubeScale m)^2 := by
  have ht := cubeScale_pos hm
  unfold coverScaleW coverGraphX
  simp only [div_pow,sq_sqrt hn]
  field_simp
  <;> ring

theorem cover_graph_coordinates_exact {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    n=4*(43/10)^3*(sOf n m)^2/(coverScaleW (coverGraphX n m))^3 ∧
    m=n^2/(2*sOf n m) := by
  have ht := cubeScale_pos hm
  have hcube := cubeScale_cube hm.le
  rw [cover_graph_w_identity hn.le hm]
  unfold sOf
  generalize htdef : cubeScale m=t at *
  constructor
  · rw [← hcube]
    field_simp
    <;> ring
  · field_simp

theorem cover_graph_budget_identity {n m : ℝ} (hn : 0 ≤ n) (hm : 0 < m) :
    coverGraphBudget n m/m=coverSampleV (coverGraphX n m) := by
  have ht := cubeScale_pos hm
  have hcube := cubeScale_cube hm.le
  rw [cover_v_w_identity,cover_graph_w_identity hn hm]
  unfold coverGraphBudget coverGraphX
  generalize htdef : cubeScale m=t at *
  rw [← hcube]
  field_simp
  <;> ring

theorem cover_graph_expansion_scale {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hxmax : coverGraphX n m ≤ 17/250) :
    coverGraphExpansion n m*coverScaleR (coverGraphX n m) (sOf n m)=n := by
  have hx := cover_graph_x_pos hn hm
  have hH := cover_h_pos hx.le
  have hd := cover_den_pos hx.le hxmax
  have ht := cubeScale_pos hm
  have hcube := cubeScale_cube hm.le
  unfold coverGraphExpansion coverScaleR
  rw [cover_graph_w_identity hn.le hm]
  unfold sOf
  field_simp
  nlinarith only [hcube]

variable {V : Type} [Fintype V] [DecidableEq V]

/-- These are the new B=4.3,A=3 coordinates of an actual graph, not the
old B=6 sampling scheme. The floor and interval lemmas apply to them. -/
theorem actual_graph_cover_coordinates (G : SimpleGraph V) (hm : 0 < Fintype.card G.edgeSet) :
    ∃ x s : ℝ, 0 < x ∧ 1 ≤ s ∧
      (Fintype.card V:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3 ∧
      (Fintype.card G.edgeSet:ℝ)=(Fintype.card V:ℝ)^2/(2*s) ∧
      coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet)/
        (Fintype.card G.edgeSet:ℝ)=coverSampleV x := by
  have hmR : (0:ℝ) < Fintype.card G.edgeSet := by exact_mod_cast hm
  have hsize := twice_graph_edges_le_order_sq G
  have hnR : (0:ℝ) < Fintype.card V := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  obtain ⟨horder,hmass⟩ := cover_graph_coordinates_exact hnR hmR
  exact ⟨coverGraphX (Fintype.card V) (Fintype.card G.edgeSet),
    sOf (Fintype.card V) (Fintype.card G.edgeSet),cover_graph_x_pos hnR hmR,
    sOf_ge_one hmR hsize,horder,hmass,cover_graph_budget_identity hnR.le hmR⟩

end
end Cycle12
