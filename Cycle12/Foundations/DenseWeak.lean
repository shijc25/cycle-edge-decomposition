import Cycle12.Foundations.EulerianPreprocessing
import Cycle12.Foundations.WeakRecycling

/-! Dense extraction followed by the proved general-graph weak-clique
theorem. The even rounding pays the five-degree preprocessing loss. -/
namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem exists_dense_induced_core_of_bounds (G : SimpleGraph V) {E N D : ℝ}
    (hD : 1 ≤ D) (hDN : D ≤ N) (horder : (Fintype.card V:ℝ) ≤ N)
    (hedges : E ≤ (G.edgeFinset.card:ℝ)) (hdense : D*N-D^2/2 ≤ E) :
    ∃ s : Finset V, s.Nonempty ∧
      ∀ v : (s:Set V), D ≤ ((G.induce (s:Set V)).degree v:ℝ) := by
  have hD0 : 0 ≤ D := by linarith
  have hcard0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hDcard : D ≤ (Fintype.card V:ℝ) := by
    by_contra h
    have hlt : (Fintype.card V:ℝ) < D := lt_of_not_ge h
    have hcomplete := inducedEdgeCount_le_complete G univ
    simp only [inducedEdgeCount_univ,card_univ] at hcomplete
    have hp : 0 < (D-Fintype.card V)*(D+Fintype.card V) :=
      mul_pos (sub_pos.mpr hlt) (by linarith)
    have hDNprod := mul_le_mul_of_nonneg_left hDN hD0
    nlinarith
  have he : D*Fintype.card V-D^2/2 ≤ (G.edgeFinset.card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left horder hD0
    linarith
  obtain ⟨s,hs,hdeg,_⟩ := exists_dense_induced_core G hD hDcard he
  exact ⟨s,hs,hdeg⟩

theorem exists_dense_budgeted_weak_model (G : SimpleGraph V) {E N D T : ℝ}
    (hT : 5 ≤ T) (hTD : 7*T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V:ℝ) ≤ N) (hedges : E ≤ (G.edgeFinset.card:ℝ))
    (hdense : D*N-D^2/2 ≤ E) :
    ∃ M : WeakCliqueImmersion (evenFloor (T-1)) G,
      (∀ i, D ≤ (G.degree (M.branch i):ℝ)) ∧
      (∀ i, 10*{e∈M.used | M.branch i∈e}.ncard ≤ 11*evenFloor (T-1)) := by
  obtain ⟨s,hs,hdeg⟩ := exists_dense_induced_core_of_bounds G (by linarith) hDN horder hedges hdense
  letI : Nonempty (s:Set V) := ⟨⟨hs.choose,hs.choose_spec⟩⟩
  obtain ⟨ht,htT,_,hteven⟩ := evenFloor_bounds (show 4 ≤ T-1 by linarith)
  have hmin : ∀ v : (s:Set V), 7*evenFloor (T-1)+5 ≤ (G.induce (s:Set V)).degree v := by
    intro v
    have hh := hdeg v
    have hr : 7*(evenFloor (T-1):ℝ)+5 ≤ ((G.induce (s:Set V)).degree v:ℝ) := by linarith
    exact_mod_cast hr
  obtain ⟨M,hM⟩ := budgeted_clique_of_min_degree (G.induce (s:Set V)) ht hteven hmin
  let f := SimpleGraph.Copy.induce G (s:Set V)
  let R := EdgeRouting.ofCopy f
  refine ⟨M.lift R,?_,M.lift_preserves_branch_budget R hM⟩
  intro i
  change D ≤ (G.degree (f (M.branch i)):ℝ)
  exact (hdeg (M.branch i)).trans (by exact_mod_cast f.degree_le (M.branch i))

theorem exists_dense_recycled_weak_model (H F K : SimpleGraph V)
    (hd : Disjoint F K) (hu : F⊔K=H) {E N D T d g : ℝ}
    (hT : 5 ≤ T) (hTD : 7*T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V:ℝ) ≤ N) (hedges : E ≤ (K.edgeFinset.card:ℝ))
    (hdense : D*N-D^2/2 ≤ E) (hg : g < 1)
    (hmark : ∀ v, D ≤ (K.degree v:ℝ) → g*H.degree v ≤ (F.degree v:ℝ))
    (hbase : ∀ v, d ≤ (H.degree v:ℝ)) :
    ∃ J : WeakCliqueImmersion (evenFloor (T-1)) H, F≤J.residue ∧
      ∀ i, max (D/(1-g)) d-11/10*T ≤ (J.residue.degree (J.branch i):ℝ) := by
  obtain ⟨M,hcore,hbudget⟩ := exists_dense_budgeted_weak_model K hT hTD hDN horder hedges hdense
  have ht : (evenFloor (T-1):ℝ) ≤ T :=
    (evenFloor_bounds (show 4 ≤ T-1 by linarith)).2.1.trans (by linarith)
  obtain ⟨J,_,hF,hdegree⟩ := recycled_weak_branch_bound H F K hd hu M hg hcore hmark
    (fun i => hbase (M.branch i)) hbudget ht
  exact ⟨J,hF,hdegree⟩

end
end Cycle13
