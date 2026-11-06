import Cycle12.Foundations.FiniteAffineStep
import Cycle12.Foundations.LongCycle
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace Cycle13
open SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem weightedAffine_mono_constant {C D t : ℝ} (hCD : C ≤ D)
    (hC : WeightedAffineBound C t) : WeightedAffineBound D t := by
  intro V _ _ G
  obtain ⟨P,hP⟩ := hC V G
  have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hCD hn
  exact ⟨P,by linarith only [hm,hP]⟩

/-- A discrete replacement for the integral completion argument.
Deleting cycles of length at least k+1 leaves at most k*n/2 edges;
the old affine bound then costs exactly 1/(2*(k+1)) more per vertex. -/
theorem weightedAffine_successor {C : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hbase : WeightedAffineBound C k) :
    WeightedAffineBound (C+1/(2*(k+1))) ((k+1:ℕ):ℝ) := by
  apply weightedAffine_of_short_cycles (by omega : 1 ≤ k+1)
  intro V _ _ G hshort
  have he : G.edgeFinset.card=G.edgeSet.ncard := by
    rw [G.edgeFinset_card,Set.fintypeCard_eq_ncard]
  have hb := Cycle12.Independent.erdosGallai_cycle G k hk
    (fun v p hp => by have hh := hshort v p hp; omega)
  rw [he] at hb
  have hb' : 2*G.edgeSet.ncard ≤ k*Fintype.card V :=
    hb.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hm : 2*(G.edgeSet.ncard:ℝ) ≤ (k:ℝ)*Fintype.card V := by exact_mod_cast hb'
  have hk₀ : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk₁ : (0:ℝ) < k+1 := by positivity
  obtain ⟨P,hP⟩ := hbase V G
  refine ⟨P,hP.trans ?_⟩
  push_cast
  have hd : (G.edgeSet.ncard:ℝ)/k ≤ (G.edgeSet.ncard:ℝ)/(k+1)+
      (Fintype.card V:ℝ)/(2*(k+1)) := by
    apply (div_le_iff₀ hk₀).mpr
    field_simp
    nlinarith only [hm]
  calc
    _ ≤ C*Fintype.card V+((G.edgeSet.ncard:ℝ)/(k+1)+(Fintype.card V:ℝ)/(2*(k+1))) :=
      add_le_add le_rfl hd
    _ = _ := by ring

theorem weightedAffine_harmonic {C : ℝ} {k u : ℕ} (hk : 2 ≤ k) (hku : k ≤ u)
    (hbase : WeightedAffineBound C k) :
    WeightedAffineBound (C+((harmonic u:ℝ)-(harmonic k:ℝ))/2) u := by
  induction u,hku using Nat.le_induction with
  | base => simpa using hbase
  | succ u hku ih =>
      have hh := weightedAffine_successor (hk.trans hku) ih
      have he : C+((harmonic (u+1):ℝ)-(harmonic k:ℝ))/2 =
          C+((harmonic u:ℝ)-(harmonic k:ℝ))/2+1/(2*(u+1)) := by
        rw [harmonic_succ]
        push_cast
        field_simp <;> ring
      rw [he]
      exact hh

/-- The harmonic remainder above any fixed positive anchor is bounded
by a logarithm, using the proved monotonicity of H_n-log n. -/
theorem harmonic_difference_log_upper {k u : ℕ} (hk : 0 < k) (hku : k ≤ u) :
    (harmonic u:ℝ)-(harmonic k:ℝ) ≤ log u-log k := by
  have hu : 0 < u := hk.trans_le hku
  have hh := Real.strictAnti_eulerMascheroniSeq'.antitone hku
  simp only [Real.eulerMascheroniSeq',hk.ne',hu.ne',ite_false] at hh
  linarith

/-- Only the small-circumference base theorem remains as a hypothesis.
No classification or finite-kernel claim is hidden in this interface. -/
theorem weightedAffine_harmonic_anchor {u a : ℕ} (ha : 7 ≤ a) (hu : a ≤ u)
    (hbase : WeightedAffineBound (19/42) 7) :
    WeightedAffineBound (19/42+((harmonic a:ℝ)-(harmonic 7:ℝ)+log u-log a)/2) u := by
  apply weightedAffine_mono_constant _ (weightedAffine_harmonic (by norm_num) (ha.trans hu) hbase)
  have hh := harmonic_difference_log_upper (by omega : 0 < a) hu
  linarith

end
end Cycle13
