import Cycle12.MetricBalls

/-! Square-root growth of actual graph balls, derived from expansion and simplicity. -/
namespace Cycle12

theorem sqrt_growth_from_layer_product {x y z h : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hy : 0 < y) (hh : 0 < h)
    (hprod : h*y ≤ (y-x)*(z-y)) :
    Real.sqrt x + Real.sqrt h ≤ Real.sqrt z := by
  have ha : 0 < y-x := by
    by_contra hn
    have heq : y-x = 0 := by linarith
    rw [heq, zero_mul] at hprod
    exact (mul_pos hh hy).not_ge hprod
  have hsq : (Real.sqrt x * Real.sqrt h)^2 = x*h := by
    rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hh.le]
  have haux : (y-x)*(Real.sqrt x+Real.sqrt h)^2 ≤ (y-x)*z := by
    have hn := sq_nonneg (y-x-Real.sqrt x*Real.sqrt h)
    have he : (y-x)*((Real.sqrt x+Real.sqrt h)^2-z) =
        h*y-(y-x)*(z-y)-(y-x-Real.sqrt x*Real.sqrt h)^2 := by
      nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hh.le]
    nlinarith
  have hb := (mul_le_mul_iff_right₀ ha).mp (by simpa only [mul_comm (y-x)] using haux)
  exact Real.le_sqrt_of_sq_le hb

universe u
variable {V : Type u} [Fintype V]
open scoped Classical

theorem metricBall_sqrt_two_step {G : SimpleGraph V} {h : ℝ} (hh : 0 < h)
    (hG : CutExpands G h) (v : V) (r : ℕ)
    (hsmall : 2*(metricBall G v (r+1)).card ≤ Fintype.card V) :
    Real.sqrt ((metricBall G v r).card : ℝ) + Real.sqrt h ≤
      Real.sqrt ((metricBall G v (r+2)).card : ℝ) := by
  have hxy := Finset.card_le_card (metricBall_mono G v (by omega : r ≤ r+1))
  have hyz := Finset.card_le_card (metricBall_mono G v (by omega : r+1 ≤ r+2))
  have hpos := Finset.card_pos.mpr (metricBall_nonempty G v (r+1))
  have he := hG (metricBall G v (r+1)) hsmall
  have hp := boundary_succ_metricBall_le_product G v r
  have hpR : (boundaryCount G (metricBall G v (r+1)) : ℝ) ≤
      ((metricBall G v (r+1)).card - (metricBall G v r).card : ℝ)*
        ((metricBall G v (r+2)).card - (metricBall G v (r+1)).card : ℝ) := by
    exact_mod_cast hp
  exact sqrt_growth_from_layer_product (Nat.cast_nonneg _) (by exact_mod_cast hxy)
    (by exact_mod_cast hyz) (by exact_mod_cast hpos) hh (he.trans hpR)

theorem metricBall_sqrt_lower {G : SimpleGraph V} {h : ℝ} (hc : G.Connected)
    (hh : 0 < h) (hG : CutExpands G h) (v : V) (r : ℕ)
    (hsmall : 2*(metricBall G v r).card ≤ Fintype.card V) :
    (r : ℝ)*Real.sqrt h/2 ≤ Real.sqrt ((metricBall G v r).card : ℝ) := by
  revert hsmall
  induction r using Nat.twoStepInduction with
  | zero =>
    intro _
    simpa using Real.sqrt_nonneg ((metricBall G v 0).card : ℝ)
  | one =>
    intro hsmall
    have hr := Real.sqrt_le_sqrt (first_metricBall_card hc hG v hsmall)
    have hn := Real.sqrt_nonneg h
    norm_num only [Nat.cast_one, one_mul]
    linarith
  | more r ihr _ =>
    intro hsmall
    have hrsmall : 2*(metricBall G v r).card ≤ Fintype.card V :=
      (Nat.mul_le_mul_left 2 (Finset.card_le_card (metricBall_mono G v (by omega : r ≤ r+2)))).trans hsmall
    have hrsmall1 : 2*(metricBall G v (r+1)).card ≤ Fintype.card V :=
      (Nat.mul_le_mul_left 2 (Finset.card_le_card (metricBall_mono G v (by omega : r+1 ≤ r+2)))).trans hsmall
    have hi := ihr hrsmall
    have ht := metricBall_sqrt_two_step hh hG v r hrsmall1
    push_cast
    nlinarith

theorem small_metricBall_radius_bound {G : SimpleGraph V} {h : ℝ} (hc : G.Connected)
    (hh : 0 < h) (hG : CutExpands G h) (v : V) (r : ℕ)
    (hsmall : 2*(metricBall G v r).card ≤ Fintype.card V) :
    (r : ℝ) ≤ Real.sqrt (2*(Fintype.card V : ℝ)/h) := by
  have hl := metricBall_sqrt_lower hc hh hG v r hsmall
  have hsq : ((r : ℝ)*Real.sqrt h/2)^2 ≤ ((metricBall G v r).card : ℝ) := by
    exact (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mp hl
  have hs : 2*((metricBall G v r).card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hsmall
  rw [div_pow, mul_pow, Real.sq_sqrt hh.le] at hsq
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hh).mpr
  nlinarith

theorem large_metricBall {G : SimpleGraph V} {h : ℝ} (hc : G.Connected)
    (hh : 0 < h) (hG : CutExpands G h) (v : V) :
    Fintype.card V < 2*(metricBall G v (⌊Real.sqrt (2*(Fintype.card V : ℝ)/h)⌋₊+1)).card := by
  by_contra hn
  have hb := small_metricBall_radius_bound hc hh hG v _ (by omega :
    2*(metricBall G v (⌊Real.sqrt (2*(Fintype.card V : ℝ)/h)⌋₊+1)).card ≤ Fintype.card V)
  have hf := Nat.lt_floor_add_one (Real.sqrt (2*(Fintype.card V : ℝ)/h))
  push_cast at hb
  linarith

end Cycle12
