import Cycle12.BallGrowth

/-! The required quadratic diameter bound, as existence of an actual simple path. -/
namespace Cycle12

universe u
variable {V : Type u} [Fintype V]
open scoped Classical
open Finset

theorem expanding_graph_dist_bound {G : SimpleGraph V} {h : ℝ}
    (hh : 0 < h) (hG : CutExpands G h) (u v : V) :
    (G.dist u v : ℝ) ≤ 2*Real.sqrt (2*(Fintype.card V : ℝ)/h)+2 := by
  haveI : Nonempty V := ⟨u⟩
  have hc := cutExpands_connected hh hG
  let R : ℕ := ⌊Real.sqrt (2*(Fintype.card V : ℝ)/h)⌋₊+1
  have hu : Fintype.card V < 2*(metricBall G u R).card := large_metricBall hc hh hG u
  have hv : Fintype.card V < 2*(metricBall G v R).card := large_metricBall hc hh hG v
  have hi : ((metricBall G u R) ∩ (metricBall G v R)).Nonempty := by
    apply Finset.not_disjoint_iff_nonempty_inter.mp
    intro hd
    have hcu := Finset.card_union_of_disjoint hd
    have hcu' : ((metricBall G u R) ∪ (metricBall G v R)).card ≤ Fintype.card V := card_le_univ _
    omega
  obtain ⟨w, hw⟩ := hi
  have huw := mem_metricBall.mp (mem_inter.mp hw).1
  have hvw := mem_metricBall.mp (mem_inter.mp hw).2
  have hdist : G.dist u v ≤ 2*R := by
    have ht := hc.dist_triangle (u := u) (v := w) (w := v)
    rw [SimpleGraph.dist_comm (G := G) (u := w) (v := v)] at ht
    omega
  have hdR : (G.dist u v : ℝ) ≤ 2*(R : ℝ) := by exact_mod_cast hdist
  have hf := Nat.floor_le (Real.sqrt_nonneg (2*(Fintype.card V : ℝ)/h))
  dsimp [R] at hdR
  push_cast at hdR
  linarith

theorem expanding_graph_short_path {G : SimpleGraph V} {h : ℝ}
    (hh : 0 < h) (hG : CutExpands G h) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧
      (p.length : ℝ) ≤ 2*Real.sqrt (2*(Fintype.card V : ℝ)/h)+2 := by
  haveI : Nonempty V := ⟨u⟩
  have hc := cutExpands_connected hh hG
  obtain ⟨p, hp, hlen⟩ := hc.exists_path_of_dist u v
  exact ⟨p, hp, hlen ▸ expanding_graph_dist_bound hh hG u v⟩

end Cycle12
