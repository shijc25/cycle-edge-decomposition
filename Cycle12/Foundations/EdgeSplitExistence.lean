import Cycle12.Foundations.BernoulliEdges
import Cycle12.Foundations.GraphBranchCut

/-! Simultaneous edge-split events. The all-cuts probability bound remains
an explicit input; degree and edge-count concentration are proved here. -/
namespace Cycle13
open SimpleGraph Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable

theorem exists_avoid_three_bad_events {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C : Set Ω)
    {a b c : ℝ} (hA : μ.real A ≤ a) (hB : μ.real B ≤ b) (hC : μ.real C ≤ c)
    (hbudget : a + b + c < 1) : ∃ ω, ω ∉ A ∧ ω ∉ B ∧ ω ∉ C := by
  have hu : μ.real (A ∪ B ∪ C) ≤ μ.real A + μ.real B + μ.real C :=
    (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le A B) le_rfl)
  by_contra hn
  have he : A ∪ B ∪ C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    by_contra hω
    apply hn
    exact ⟨ω, fun h => hω (Or.inl (Or.inl h)),
      fun h => hω (Or.inl (Or.inr h)), fun h => hω (Or.inr h)⟩
  rw [he] at hu
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hu
  simp only [Measure.real] at hA hB hC
  linarith

theorem exists_simultaneous_edge_split {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : unitInterval) {D g f ε a b c : ℝ}
    (hD : 0 < D) (hg₀ : 0 ≤ g) (hgq : g < (q : ℝ)) (hε : 0 ≤ ε)
    (hcut : (edgeSplitMeasure V q).real
      {ω | ¬∀ S : Finset V, f * cutSize G S ≤ (cutSize (splitBank G ω true) S : ℝ)} ≤ a)
    (hcore : exp (-2 * ε ^ 2 * G.edgeSet.ncard) ≤ b)
    (hbranch : (g = f ∧ 0 ≤ c) ∨
      Fintype.card V * exp (-2 * D * ((q : ℝ) - g) ^ 2 / (1 - g)) ≤ c)
    (hbudget : a + b + c < 1) :
    ∃ ω : Sym2 V → Bool,
      (∀ S : Finset V, f * cutSize G S ≤ (cutSize (splitBank G ω true) S : ℝ)) ∧
      (1 - (q : ℝ) - ε) * G.edgeSet.ncard ≤ ((splitBank G ω false).edgeSet.ncard : ℝ) ∧
      (∀ v : V, D ≤ ((splitBank G ω false).degree v : ℝ) →
        g * G.degree v ≤ ((splitBank G ω true).degree v : ℝ)) := by
  let P := fun ω : Sym2 V → Bool =>
    ∀ S : Finset V, f * cutSize G S ≤ (cutSize (splitBank G ω true) S : ℝ)
  let A : Set (Sym2 V → Bool) := {ω | ¬P ω}
  let B : Set (Sym2 V → Bool) := {ω |
    ((splitBank G ω false).edgeSet.ncard : ℝ) < (1 - (q : ℝ) - ε) * G.edgeSet.ncard}
  let C : Set (Sym2 V → Bool) := {ω | P ω ∧ ∃ v : V,
    D ≤ ((splitBank G ω false).degree v : ℝ) ∧
      ((splitBank G ω true).degree v : ℝ) < g * G.degree v}
  have hB : (edgeSplitMeasure V q).real B ≤ b :=
    (edge_split_core_edge_failure G q hε).trans hcore
  have hC : (edgeSplitMeasure V q).real C ≤ c := by
    rcases hbranch with ⟨hgf, hc⟩ | hb
    · have he : C = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ω ⟨hP, v, _, hv⟩
        have hd := cut_retention_implies_degree_retention G (splitBank G ω true) hP v
        rw [hgf] at hv
        exact not_lt_of_ge hd hv
      rw [he, measureReal_empty]
      exact hc
    · have hsub : C ⊆ {ω | ∃ v : V, D ≤ ((splitBank G ω false).degree v : ℝ) ∧
          ((splitBank G ω true).degree v : ℝ) < g * G.degree v} := fun _ h => h.2
      exact (measureReal_mono hsub).trans ((edge_split_branch_failure G q hD hg₀ hgq).trans hb)
  obtain ⟨ω, hA, hB, hC⟩ := exists_avoid_three_bad_events (edgeSplitMeasure V q) A B C hcut hB hC hbudget
  have hP : P ω := by simpa only [A, Set.mem_ofPred_eq, not_not] using hA
  refine ⟨ω, hP, le_of_not_gt hB, ?_⟩
  intro v hv
  by_contra hbad
  exact hC ⟨hP, v, hv, lt_of_not_ge hbad⟩

end
end Cycle13
