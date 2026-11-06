import Cycle12.Foundations.ListLinkAssembly
import Cycle12.Foundations.WeakBranchBudget

/-! The small-p carrier case: two genuine list-coloured path banks give a
strong clique immersion. Existing branch-to-branch edges are not needed. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def cliqueOn {W : Type} (C : Finset W) : SimpleGraph W where
  Adj x y := x ≠ y ∧ x ∈ C ∧ y ∈ C
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma cliqueOn_support {W : Type} (C : Finset W) :
    (cliqueOn C).support ⊆ (C : Set W) := by
  intro v hv
  obtain ⟨w,hw⟩ := (cliqueOn C).mem_support.mp hv
  exact hw.2.1

lemma cliqueOn_degree_le {W : Type} [Fintype W] [DecidableEq W] (C : Finset W) (v : W) :
    (cliqueOn C).degree v ≤ C.card := by
  rw [← card_neighborFinset_eq_degree]
  apply card_le_card
  intro w hw
  have hw' : (cliqueOn C).Adj v w := by simpa using hw
  exact hw'.2.2

lemma cliqueOn_degree_zero {W : Type} [Fintype W] [DecidableEq W] (C : Finset W)
    (v : W) (hv : v ∉ C) : (cliqueOn C).degree v=0 := by
  apply IsIsolated.degree_eq_zero
  intro w hw
  exact hv hw.2.1

theorem exists_small_carrier_path_banks {W V : Type} [Fintype W] [DecidableEq W]
    [DecidableEq V] (G : SimpleGraph V) (C : Finset W) (D : Finset V) (φ : W ↪ V)
    {t p ρ : ℕ} (hcard : Fintype.card W=t) (hp : p ≤ t) (hC : C.card=t-p)
    (hρ : ρ ≤ p) (hsmall : 4*p ≤ 3*t) (hD : 6*t+ρ ≤ D.card)
    (hout : ∀ v, φ v ∉ D)
    (hold : ∀ v, v ∉ C → missingNeighbors G D (φ v) ≤ 2*p+ρ)
    (hnew : ∀ v, v ∈ C → missingNeighbors G D (φ v) ≤ t+2*p+ρ) :
    ∃ L : ReservoirLinks (cliqueOn C) G D φ,
      Nonempty (ReservoirLinks (cliqueOn C)ᶜ L.residue D φ) := by
  obtain ⟨L⟩ := exists_reservoir_links_supported (cliqueOn C) G D φ C
    (cliqueOn_support C) (by
      intro x y hxy
      have hx := hnew x hxy.2.1
      have hy := hnew y hxy.2.2
      omega)
  refine ⟨L,exists_reservoir_links _ _ _ _ ?_⟩
  intro x y hxy
  have hx := L.missing_residue_le hout x
  have hy := L.missing_residue_le hout y
  rw [hcard]
  have hxy' := (compl_adj (cliqueOn C) x y).mp hxy
  by_cases hxC : x ∈ C <;> by_cases hyC : y ∈ C
  · exact False.elim (hxy'.2 ⟨hxy'.1,hxC,hyC⟩)
  · have hx' := hnew x hxC
    have hy' := hold y hyC
    have hdx := cliqueOn_degree_le C x
    rw [cliqueOn_degree_zero C y hyC] at hy
    omega
  · have hx' := hold x hxC
    have hy' := hnew y hyC
    have hdy := cliqueOn_degree_le C y
    rw [cliqueOn_degree_zero C x hxC] at hx
    omega
  · have hx' := hold x hxC
    have hy' := hold y hyC
    rw [cliqueOn_degree_zero C x hxC] at hx
    rw [cliqueOn_degree_zero C y hyC] at hy
    omega

theorem strong_model_of_small_carrier {V : Type} [DecidableEq V] {t p ρ : ℕ}
    (G : SimpleGraph V) (C : Finset (Fin t)) (D : Finset V) (φ : Fin t ↪ V)
    (hp : p ≤ t) (hC : C.card=t-p) (hρ : ρ ≤ p) (hsmall : 4*p ≤ 3*t)
    (hD : 6*t+ρ ≤ D.card) (hout : ∀ v, φ v ∉ D)
    (hold : ∀ v, v ∉ C → missingNeighbors G D (φ v) ≤ 2*p+ρ)
    (hnew : ∀ v, v ∈ C → missingNeighbors G D (φ v) ≤ t+2*p+ρ) :
    Nonempty (StrongCliqueImmersion t G) := by
  obtain ⟨L,⟨K⟩⟩ := exists_small_carrier_path_banks G C D φ
    (Fintype.card_fin t) hp hC hρ hsmall hD hout hold hnew
  let R := L.completeRouting K hout
  refine ⟨{
    branch := φ
    route := fun e => (R.route (ne_of_lt e.2)).toPath
    disjoint := ?_
    avoids := ?_ }⟩
  · intro e d hed
    exact (R.disjoint (ne_of_lt e.2) (ne_of_lt d.2)
      (fun h => hed (CliquePair.edge_injective h))).mono
      (R.route (ne_of_lt e.2)).edges_toPath_subset_edges
      (R.route (ne_of_lt d.2)).edges_toPath_subset_edges
  · intro e i hi
    exact R.avoids _ i ((R.route (ne_of_lt e.2)).support_toPath_subset_support hi)

end
end Cycle13
