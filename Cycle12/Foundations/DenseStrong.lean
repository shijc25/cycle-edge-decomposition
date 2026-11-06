import Cycle12.Foundations.CoreExtraction
import Cycle12.Foundations.StrongStopping
import Cycle12.Foundations.ImmersionMap

/-! Dense-core extraction followed by the actual strong-immersion stopping
theorem. All graph and path existence statements here are unconditional. -/
namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

def evenFloor (T : ℝ) : ℕ := 2 * ⌊T / 2⌋₊

theorem evenFloor_bounds {T : ℝ} (hT : 4 ≤ T) :
    4 ≤ evenFloor T ∧ (evenFloor T : ℝ) ≤ T ∧ T - 2 < (evenFloor T : ℝ) ∧
      Even (evenFloor T) := by
  have hf : 2 ≤ ⌊T / 2⌋₊ := Nat.le_floor (by linarith)
  have hlo := Nat.floor_le (show (0 : ℝ) ≤ T / 2 by linarith)
  have hhi := Nat.lt_floor_add_one (T / 2)
  refine ⟨by dsimp [evenFloor]; omega, ?_, ?_, ?_⟩
  · dsimp [evenFloor]
    push_cast
    linarith
  · dsimp [evenFloor]
    push_cast
    linarith
  · exact ⟨⌊T / 2⌋₊, by dsimp [evenFloor]; omega⟩

theorem exists_dense_core_strong_immersion {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) {E N D T : ℝ} {t : ℕ}
    (ht : 3 ≤ t) (htT : (t : ℝ) ≤ T)
    (hD : 1 ≤ D) (hTD : T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V : ℝ) ≤ N)
    (hedges : E ≤ (G.edgeFinset.card : ℝ))
    (hdense : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + log (N / T)) ≤ 2 * E / N) :
    ∃ s : Finset V, s.Nonempty ∧ D < (s.card : ℝ) ∧
      (∀ v : (s : Set V), D ≤ (G.induce (s : Set V)).degree v) ∧
      E - D * (N - s.card) ≤ inducedEdgeCount G s ∧
      Nonempty (StrongCliqueImmersion t (G.induce (s : Set V))) := by
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hT : 0 < T := by linarith
  obtain ⟨s, hs, hsD, hdeg, hret, havg⟩ :=
    exists_dense_core_with_average G hT hD hTD hDN horder hedges hdense hstop
  have htn : (t : ℝ) < s.card := htT.trans_lt (hTD.trans_lt hsD)
  have htnNat : t < s.card := by exact_mod_cast htn
  have hstrict := strict_stopping_threshold
    (a := (t : ℝ) - 2) (n := (s.card : ℝ))
    (by linarith) (by linarith) (hTD.trans_lt hsD) (by linarith)
  have hc : Fintype.card (s : Set V) = s.card := Fintype.card_coe _
  refine ⟨s, hs, hsD, hdeg, hret, strong_clique_of_average_log ht _ ?_ ?_⟩
  · rw [hc]
    omega
  · have hcount : (G.induce (s : Set V)).edgeSet.ncard = inducedEdgeCount G s := by
      simp only [inducedEdgeCount, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    simpa only [logStoppingThreshold, averageDegree, hc, hcount]
      using hstrict.trans_le havg

/-- Exact even rounding used by the coefficient-13 dense strong bank. -/
theorem exists_dense_even_strong_core {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) {E N D T : ℝ}
    (hT : 4 ≤ T) (hTD : T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V : ℝ) ≤ N)
    (hedges : E ≤ (G.edgeFinset.card : ℝ))
    (hdense : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + log (N / T)) ≤ 2 * E / N) :
    ∃ s : Finset V, s.Nonempty ∧ D < (s.card : ℝ) ∧
      (∀ v : (s : Set V), D ≤ (G.induce (s : Set V)).degree v) ∧
      E - D * (N - s.card) ≤ inducedEdgeCount G s ∧
      Nonempty (StrongCliqueImmersion (evenFloor T) (G.induce (s : Set V))) := by
  obtain ⟨ht, htT, _⟩ := evenFloor_bounds hT
  exact exists_dense_core_strong_immersion G (by omega) htT (by linarith)
    hTD hDN horder hedges hdense hstop

/-- The strong model lies in the original graph, and every branch retains
the dense-core degree guarantee in that graph. -/
theorem exists_dense_even_strong_model {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) {E N D T : ℝ}
    (hT : 4 ≤ T) (hTD : T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V : ℝ) ≤ N)
    (hedges : E ≤ (G.edgeFinset.card : ℝ))
    (hdense : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + log (N / T)) ≤ 2 * E / N) :
    ∃ M : StrongCliqueImmersion (evenFloor T) G,
      ∀ i : Fin (evenFloor T), D ≤ G.degree (M.branch i) := by
  obtain ⟨s, _, _, hdeg, _, ⟨M⟩⟩ :=
    exists_dense_even_strong_core G hT hTD hDN horder hedges hdense hstop
  let f : (G.induce (s : Set V)).Copy G := SimpleGraph.Copy.induce G (s : Set V)
  refine ⟨M.mapCopy f, ?_⟩
  intro i
  rw [StrongCliqueImmersion.mapCopy_branch]
  exact (hdeg (M.branch i)).trans (by exact_mod_cast f.degree_le (M.branch i))

end
end Cycle13
