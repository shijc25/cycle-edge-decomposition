import Cycle12.Foundations.SplitRouting
import Cycle12.Foundations.DenseCoreAnalytic

/-! The logarithmic stopping criterion for strong clique immersions.
The order restriction `t-1 ≤ n` is essential and is stated explicitly. -/
namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem logarithmic_stop_step {a n : ℝ} (ha : 0 < a) (hn : 2 < n) :
    a * (1 + log ((n - 2) / a)) ≤
      a * (1 + log ((n - 1) / a)) - a / (n - 1) := by
  have hn1 : 0 < n - 1 := by linarith
  have hn2 : 0 < n - 2 := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hn1 hn2)
  have hfrac : 1 - ((n - 1) / (n - 2))⁻¹ = 1 / (n - 1) := by
    rw [inv_div]
    field_simp
    ring
  rw [hfrac] at hl
  have hlog : log ((n - 1) / a) = log ((n - 2) / a) + log ((n - 1) / (n - 2)) := by
    rw [Real.log_div hn1.ne' ha.ne', Real.log_div hn2.ne' ha.ne',
      Real.log_div hn1.ne' hn2.ne']
    ring
  have hm := mul_le_mul_of_nonneg_left hl ha.le
  rw [mul_one_div] at hm
  rw [hlog]
  nlinarith

def averageDegree {V : Type} [Fintype V] (G : SimpleGraph V) : ℝ :=
  2 * G.edgeSet.ncard / Fintype.card V

def logStoppingThreshold (t n : ℕ) : ℝ :=
  ((t : ℝ) - 2) * (1 + log (((n : ℝ) - 1) / ((t : ℝ) - 2)))

theorem averageDegree_le_order_sub_one {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : averageDegree G ≤ (Fintype.card V : ℝ) - 1 := by
  classical
  have h := G.card_edgeFinset_le_card_choose_two
  have hcast : (G.edgeSet.ncard : ℝ) ≤
      (Fintype.card V : ℝ) * (Fintype.card V - 1) / 2 := by
    have hh : (G.edgeFinset.card : ℝ) ≤ (Fintype.card V).choose 2 := by exact_mod_cast h
    rw [Nat.cast_choose_two] at hh
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hh
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  apply (div_le_iff₀ hn).mpr
  nlinarith

theorem exists_degree_le_average {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : ∃ u : V, (G.degree u : ℝ) ≤ averageDegree G := by
  classical
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  have hmin : ∀ v : V, (G.degree u : ℝ) ≤ G.degree v := by
    intro v
    exact_mod_cast (hu ▸ G.minDegree_le_degree v)
  have hs : (∑ v : V, (G.degree v : ℝ)) = 2 * G.edgeSet.ncard := by
    have hnat := G.sum_degrees_eq_twice_card_edges
    simp only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] at hnat
    exact_mod_cast hnat
  have hbound : (Fintype.card V : ℝ) * G.degree u ≤ 2 * G.edgeSet.ncard := by
    calc
      _ = ∑ _v : V, (G.degree u : ℝ) := by simp
      _ ≤ ∑ v : V, (G.degree v : ℝ) := sum_le_sum (fun v _ => hmin v)
      _ = _ := hs
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  refine ⟨u, (le_div_iff₀ hn).mpr ?_⟩
  simpa only [mul_comm] using hbound

theorem logStoppingThreshold_step {t n : ℕ} (ht : 3 ≤ t) (hn : 3 ≤ n) :
    logStoppingThreshold t (n - 1) ≤
      logStoppingThreshold t n - ((t : ℝ) - 2) / ((n : ℝ) - 1) := by
  have htR : (2 : ℝ) < t := by exact_mod_cast (show 2 < t by omega)
  have hnR : (2 : ℝ) < n := by exact_mod_cast (show 2 < n by omega)
  have h := logarithmic_stop_step (a := (t : ℝ) - 2) (by linarith) hnR
  have hncast : ((n - 1 : ℕ) : ℝ) - 1 = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
    ring
  simpa only [logStoppingThreshold, hncast] using h

theorem strong_clique_of_average_log {t : ℕ} (ht : 3 ≤ t)
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (horder : t - 1 ≤ Fintype.card V)
    (hstop : logStoppingThreshold t (Fintype.card V) < averageDegree G) :
    Nonempty (StrongCliqueImmersion t G) := by
  classical
  suffices haux : ∀ n : ℕ, ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → t - 1 ≤ n →
      logStoppingThreshold t n < averageDegree H →
      Nonempty (StrongCliqueImmersion t H) by
    exact haux _ V G rfl horder hstop
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W inst H hcard hord hstrict
    have hn2 : 2 ≤ n := by omega
    have hWpos : 0 < Fintype.card W := by omega
    have : Nonempty W := Fintype.card_pos_iff.mp hWpos
    by_cases hbase : n = t - 1
    · have havg := averageDegree_le_order_sub_one H
      rw [hcard] at havg
      have hrel : (n : ℝ) - 1 = (t : ℝ) - 2 := by
        have hnat : n + 1 = t := by omega
        have hr : (n : ℝ) + 1 = t := by exact_mod_cast hnat
        linarith
      have ha : (t : ℝ) - 2 ≠ 0 := by
        have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
        linarith
      have hth : logStoppingThreshold t n = (n : ℝ) - 1 := by
        simp only [logStoppingThreshold, hrel, div_self ha, log_one, add_zero, mul_one]
      rw [hth] at hstrict
      exact (not_lt_of_ge havg hstrict).elim
    · by_cases hfree : H.CliqueFree t
      · have hn3 : 3 ≤ n := by omega
        obtain ⟨u, hu⟩ := exists_degree_le_average H
        obtain ⟨M, hM, havg⟩ := exists_split_average_bound H u (by omega) hfree (by omega) hu
        have hc' : Fintype.card ({u}ᶜ : Set W) = n - 1 := by
          simpa only [hcard] using split_order H u M
        have hstep := logStoppingThreshold_step ht hn3
        have havg' : averageDegree (splitGraph H u M) ≥
            averageDegree H - ((t : ℝ) - 2) / ((n : ℝ) - 1) := by
          unfold averageDegree
          rw [hc', Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
          simpa only [averageDegree, hcard] using havg
        have hstrict' : logStoppingThreshold t (n - 1) < averageDegree (splitGraph H u M) := by
          linarith
        exact strong_clique_lifts_through_split H u M hM
          (ih (n - 1) (by omega) ({u}ᶜ : Set W) (splitGraph H u M) hc' (by omega) hstrict')
      · exact StrongCliqueImmersion.exists_of_not_cliqueFree hfree

end
end Cycle13
