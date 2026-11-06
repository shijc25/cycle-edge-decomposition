import Cycle12.ExpansionConnectivity

/-! Finite metric balls and the actual two-layer cut bound used by the diameter proof. -/
namespace Cycle12

universe u
variable {V : Type u} [Fintype V]
open scoped Classical
open Finset

noncomputable def metricBall (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V :=
  univ.filter (fun w => G.dist v w ≤ r)

theorem mem_metricBall {G : SimpleGraph V} {v w : V} {r : ℕ} :
    w ∈ metricBall G v r ↔ G.dist v w ≤ r := by simp [metricBall]

theorem metricBall_mono (G : SimpleGraph V) (v : V) {r s : ℕ} (hrs : r ≤ s) :
    metricBall G v r ⊆ metricBall G v s := by
  intro w hw
  exact mem_metricBall.mpr ((mem_metricBall.mp hw).trans hrs)

theorem metricBall_nonempty (G : SimpleGraph V) (v : V) (r : ℕ) :
    (metricBall G v r).Nonempty := ⟨v, by simp [metricBall]⟩

theorem metricBall_zero {G : SimpleGraph V} (hc : G.Connected) (v : V) :
    metricBall G v 0 = {v} := by
  ext w
  simp only [mem_metricBall, Nat.le_zero, (hc v w).dist_eq_zero_iff, mem_singleton]
  exact eq_comm

theorem adjacent_dist_le {G : SimpleGraph V} {v w : V} (hadj : G.Adj v w) (c : V) :
    G.dist c w ≤ G.dist c v + 1 := by
  have ht := hadj.reachable.dist_triangle_right c
  simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] using ht

theorem boundary_metricBall_eq_cut (G : SimpleGraph V) (v : V) (r : ℕ) :
    boundaryCount G (metricBall G v r) =
      cutCount G (metricBall G v r) (metricBall G v (r+1) \ metricBall G v r) := by
  simp only [boundaryCount, cutCount_eq_filter_card]
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨heG, x, hx, y, hy, rfl⟩
    have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp heG
    have hyout : y ∈ metricBall G v (r+1) :=
      mem_metricBall.mpr ((adjacent_dist_le hxy v).trans (Nat.add_le_add_right (mem_metricBall.mp hx) 1))
    exact ⟨heG, x, hx, y, mem_sdiff.mpr ⟨hyout, mem_compl.mp hy⟩, rfl⟩
  · rintro ⟨heG, x, hx, y, hy, rfl⟩
    exact ⟨heG, x, hx, y, mem_compl.mpr (mem_sdiff.mp hy).2, rfl⟩

theorem boundary_succ_metricBall_eq_cut (G : SimpleGraph V) (v : V) (r : ℕ) :
    boundaryCount G (metricBall G v (r+1)) =
      cutCount G (metricBall G v (r+1) \ metricBall G v r)
        (metricBall G v (r+2) \ metricBall G v (r+1)) := by
  rw [boundary_metricBall_eq_cut]
  simp only [cutCount_eq_filter_card]
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨heG, x, hx, y, hy, rfl⟩
    have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp heG
    have hxnot : x ∉ metricBall G v r := by
      intro hxsmall
      have hyle : G.dist v y ≤ r+1 :=
        (adjacent_dist_le hxy v).trans (Nat.add_le_add_right (mem_metricBall.mp hxsmall) 1)
      exact (mem_sdiff.mp hy).2 (mem_metricBall.mpr hyle)
    exact ⟨heG, x, mem_sdiff.mpr ⟨hx, hxnot⟩, y, hy, rfl⟩
  · rintro ⟨heG, x, hx, y, hy, rfl⟩
    exact ⟨heG, x, (mem_sdiff.mp hx).1, y, hy, rfl⟩

theorem boundary_succ_metricBall_le_product (G : SimpleGraph V) (v : V) (r : ℕ) :
    boundaryCount G (metricBall G v (r+1)) ≤
      ((metricBall G v (r+1)).card - (metricBall G v r).card)*
        ((metricBall G v (r+2)).card - (metricBall G v (r+1)).card) := by
  rw [boundary_succ_metricBall_eq_cut]
  have hb := cutCount_le_product G (metricBall G v (r+1) \ metricBall G v r)
    (metricBall G v (r+2) \ metricBall G v (r+1))
  simpa only [card_sdiff_of_subset (metricBall_mono G v (by omega : r ≤ r+1)),
    card_sdiff_of_subset (metricBall_mono G v (by omega : r+1 ≤ r+2))] using hb

theorem first_metricBall_card {G : SimpleGraph V} {h : ℝ} (hc : G.Connected)
    (hG : CutExpands G h) (v : V)
    (hsmall : 2*(metricBall G v 1).card ≤ Fintype.card V) :
    h ≤ ((metricBall G v 1).card : ℝ) := by
  have hb := hG (metricBall G v 0)
    ((Nat.mul_le_mul_left 2 (card_le_card (metricBall_mono G v (by omega : 0 ≤ 1)))).trans hsmall)
  have hu := cutCount_le_product G (metricBall G v 0)
    (metricBall G v 1 \ metricBall G v 0)
  have hz := metricBall_zero hc v
  rw [boundary_metricBall_eq_cut] at hb
  have hcount : (metricBall G v 0).card = 1 := by simp [hz]
  rw [hcount, Nat.cast_one, mul_one] at hb
  have hu' : cutCount G (metricBall G v 0) (metricBall G v 1 \ metricBall G v 0) ≤
      (metricBall G v 1).card := by
    simp only [hcount, one_mul] at hu
    exact hu.trans (card_le_card sdiff_subset)
  exact hb.trans (by exact_mod_cast hu')

end Cycle12
