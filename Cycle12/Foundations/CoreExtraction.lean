import Cycle12.Foundations.DenseCoreAnalytic

/-! A dense induced core, chosen by maximizing an edge-minus-vertex potential.
This supplies the graph extraction step; it does not assume any immersion theorem. -/
namespace Cycle13
open Finset SimpleGraph

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def inducedEdgeCount (G : SimpleGraph V) (s : Finset V) : ℕ :=
  (G.induce (s : Set V)).edgeFinset.card

theorem inducedEdgeCount_univ (G : SimpleGraph V) :
    inducedEdgeCount G univ = G.edgeFinset.card := by
  unfold inducedEdgeCount
  rw [← G.card_filter_edgeFinset_toFinset_subset univ]
  simp

omit [Fintype V] in
theorem inducedEdgeCount_erase (G : SimpleGraph V) (s : Finset V)
    {v : V} (hv : v ∈ s) :
    inducedEdgeCount G (s.erase v) + (G.induce (s : Set V)).degree ⟨v, hv⟩ =
      inducedEdgeCount G s := by
  let H := G.induce (s : Set V)
  let w : (s : Set V) := ⟨v, hv⟩
  let e : G.induce (s.erase v : Set V) ≃g H.induce {w}ᶜ :=
    { toFun := fun x => ⟨⟨x.1, (mem_erase.mp x.2).2⟩, by
        intro hx
        exact (mem_erase.mp x.2).1 (congrArg Subtype.val hx)⟩
      invFun := fun x => ⟨x.1.1, mem_erase.mpr ⟨by
        intro hx
        exact x.2 (Subtype.ext hx), x.1.2⟩⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext (Subtype.ext rfl)
      map_rel_iff' := Iff.rfl }
  have he := e.card_edgeFinset_eq
  rw [H.card_edgeFinset_induce_compl_singleton,
    H.card_edgeFinset_deleteIncidenceSet] at he
  change inducedEdgeCount G (s.erase v) = inducedEdgeCount G s - H.degree w at he
  rw [he]
  exact Nat.sub_add_cancel (H.degree_le_card_edgeFinset w)

omit [Fintype V] [DecidableEq V] in
theorem inducedEdgeCount_le_complete (G : SimpleGraph V) (s : Finset V) :
    (inducedEdgeCount G s : ℝ) ≤ (s.card : ℝ) * (s.card - 1) / 2 := by
  have h := (G.induce (s : Set V)).card_edgeFinset_le_card_choose_two
  have hc : Fintype.card (s : Set V) = s.card := Fintype.card_coe _
  rw [hc] at h
  exact (Nat.cast_le.mpr h).trans_eq (Nat.cast_choose_two (K := ℝ) s.card)

/-- A simple graph on a number of vertices in `[D,D+1)` cannot attain the
required potential. This is what prevents a maximizer from stopping too early. -/
theorem thin_core_potential_bound {D m e : ℝ}
    (hD : 1 ≤ D) (hDm : D ≤ m) (hmD : m < D + 1)
    (he : e ≤ m * (m - 1) / 2) : e - D * m < -(D ^ 2) / 2 := by
  have hd0 : 0 ≤ m - D := sub_nonneg.mpr hDm
  have hd1 : m - D < 1 := by linarith
  have hs : (m - D) ^ 2 < 1 := by nlinarith
  nlinarith

/-- Actual graph extraction, with a real degree threshold and exact edge loss. -/
theorem exists_dense_induced_core (G : SimpleGraph V) {D : ℝ}
    (hD : 1 ≤ D) (hDN : D ≤ Fintype.card V)
    (hE : D * Fintype.card V - D ^ 2 / 2 ≤ (G.edgeFinset.card : ℝ)) :
    ∃ s : Finset V, s.Nonempty ∧
      (∀ v : (s : Set V), D ≤ (G.induce (s : Set V)).degree v) ∧
      (G.edgeFinset.card : ℝ) - D * (Fintype.card V - s.card) ≤
        inducedEdgeCount G s := by
  let candidates : Finset (Finset V) := univ.filter (fun s => D ≤ (s.card : ℝ))
  let potential : Finset V → ℝ := fun s => (inducedEdgeCount G s : ℝ) - D * s.card
  have hfull : (univ : Finset V) ∈ candidates := by
    simp only [candidates, mem_filter, mem_univ, true_and, card_univ]
    exact hDN
  obtain ⟨s, hs, hmax⟩ := candidates.exists_max_image potential ⟨univ, hfull⟩
  have hsD : D ≤ (s.card : ℝ) := (mem_filter.mp hs).2
  have hretained := hmax univ hfull
  simp only [potential, inducedEdgeCount_univ, card_univ] at hretained
  have hpotential : -(D ^ 2) / 2 ≤ (inducedEdgeCount G s : ℝ) - D * s.card := by
    linarith
  have hne : s.Nonempty := by
    apply card_pos.mp
    by_contra h
    have hz : s.card = 0 := Nat.eq_zero_of_not_pos h
    simp only [hz, Nat.cast_zero] at hsD
    linarith
  refine ⟨s, hne, ?_, by linarith⟩
  intro v
  have hcard : ((s.erase v.1).card : ℝ) + 1 = (s.card : ℝ) := by
    exact_mod_cast card_erase_add_one v.2
  have heraseD : D ≤ ((s.erase v.1).card : ℝ) := by
    by_contra h
    have hthin := thin_core_potential_bound hD hsD (show (s.card : ℝ) < D + 1 by
      push Not at h
      linarith) (inducedEdgeCount_le_complete G s)
    linarith
  have herase : s.erase v.1 ∈ candidates := by
    simp only [candidates, mem_filter, mem_univ, true_and]
    exact heraseD
  have hstep := hmax (s.erase v.1) herase
  have hcount : (inducedEdgeCount G (s.erase v.1) : ℝ) +
      (G.induce (s : Set V)).degree v = inducedEdgeCount G s := by
    exact_mod_cast inducedEdgeCount_erase G s v.2
  dsimp only [potential] at hstep
  nlinarith

/-- The extracted core has both the required minimum degree and the logarithmic
average-degree bound. The ambient order and initial edge bound may be real. -/
theorem exists_dense_core_with_average (G : SimpleGraph V) {E N D T : ℝ}
    (hT : 0 < T) (hD : 1 ≤ D) (hTD : T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V : ℝ) ≤ N)
    (hedges : E ≤ (G.edgeFinset.card : ℝ))
    (hdense : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + Real.log (N / T)) ≤ 2 * E / N) :
    ∃ s : Finset V, s.Nonempty ∧ D < (s.card : ℝ) ∧
      (∀ v : (s : Set V), D ≤ (G.induce (s : Set V)).degree v) ∧
      E - D * (N - s.card) ≤ inducedEdgeCount G s ∧
      T * (1 + Real.log ((s.card : ℝ) / T)) ≤
        2 * (inducedEdgeCount G s : ℝ) / s.card := by
  have hD0 : 0 ≤ D := by linarith
  have hcard0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hDcard : D ≤ (Fintype.card V : ℝ) := by
    by_contra h
    have hlt : (Fintype.card V : ℝ) < D := lt_of_not_ge h
    have hcomplete := inducedEdgeCount_le_complete G univ
    simp only [inducedEdgeCount_univ, card_univ] at hcomplete
    have hprod : 0 < (D - Fintype.card V) * (D + Fintype.card V) :=
      mul_pos (sub_pos.mpr hlt) (by linarith)
    have hDNprod : D * D ≤ D * N := mul_le_mul_of_nonneg_left hDN hD0
    nlinarith
  have hreal_dense : D * Fintype.card V - D ^ 2 / 2 ≤
      (G.edgeFinset.card : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left horder hD0
    linarith
  obtain ⟨s, hs, hdeg, hretained⟩ := exists_dense_induced_core G hD hDcard hreal_dense
  have hsD : D < (s.card : ℝ) := by
    obtain ⟨v, hv⟩ := hs
    have hvdeg := hdeg ⟨v, hv⟩
    have hvcard := (G.induce (s : Set V)).degree_lt_card_verts ⟨v, hv⟩
    have hc : Fintype.card (s : Set V) = s.card := Fintype.card_coe _
    rw [hc] at hvcard
    exact hvdeg.trans_lt (by exact_mod_cast hvcard)
  have hsN : (s.card : ℝ) ≤ N :=
    (show (s.card : ℝ) ≤ Fintype.card V by exact_mod_cast card_le_univ s).trans horder
  have hretained' : E - D * (N - s.card) ≤ inducedEdgeCount G s := by
    have hm := mul_le_mul_of_nonneg_left horder hD0
    linarith
  exact ⟨s, hs, hsD, hdeg, hretained',
    dense_core_average_bound hT hTD hsD.le hsN hdense hstop hretained'⟩

end
end Cycle13
