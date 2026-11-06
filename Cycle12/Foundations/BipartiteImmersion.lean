import Cycle12.Foundations.DirectLinkAssembly

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem strong_model_of_complete_bipartite {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Set V) (t : ℕ) (hAB : Disjoint A B)
    (hA : t ≤ A.ncard) (hB : t ≤ B.ncard)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    Nonempty (StrongCliqueImmersion t G) := by
  classical
  have hAcard : A.ncard=((Set.toFinite A).toFinset).card := Set.ncard_eq_toFinset_card _
  obtain ⟨φ,hφ⟩ := Function.Embedding.exists_of_card_le_finset
    (s := (Set.toFinite A).toFinset)
    (show Fintype.card (Fin t) ≤ ((Set.toFinite A).toFinset).card by
      rw [Fintype.card_fin,← hAcard]
      exact hA)
  have hφA : ∀ i, φ i ∈ A := by
    intro i
    simpa using hφ (Set.mem_range_self i)
  let D := (Set.toFinite B).toFinset
  have hD : D.card=B.ncard := (Set.ncard_eq_toFinset_card _).symm
  have hmissing : ∀ i, missingNeighbors G D (φ i)=0 := by
    intro i
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hbD,hnot⟩ := mem_filter.mp hb
    exact hnot (hcross _ (hφA i) b (by simpa [D] using hbD))
  obtain ⟨L⟩ := exists_reservoir_links (completeGraph (Fin t)) G D φ (by
    intro i j _
    rw [Fintype.card_fin,hmissing,hmissing,hD]
    simpa using hB)
  exact ⟨(L.routing (fun i hi => Set.disjoint_left.mp hAB (hφA i)
    (by simpa [D] using hi))).cliqueModel⟩

end
end Cycle13
