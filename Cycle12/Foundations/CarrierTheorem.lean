import Cycle12.Foundations.CarrierPreparation
import Cycle12.Foundations.SmallCarrier

/-! Both carrier regimes combined. The hypotheses are solely the concrete
carrier's missing-neighbour inequalities, not existence of any path bank. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem budgeted_model_of_carrier {V : Type} [Fintype V] [DecidableEq V]
    {p q : ℕ} (G : SimpleGraph V) (D : Finset V) (φ : (Fin p ⊕ Fin q) ↪ V)
    (hout : ∀ v, φ v ∉ D) (hq : 0 < q) (ht : 4 ≤ p+q) (heven : Even (p+q))
    (ρ : ℕ) (hρ : ρ ≤ p) (r : Fin p → ℕ)
    (hr : ∀ s, r s ≤ s.val+1) (hrρ : ∀ s, r s ≤ ρ) (hD : 6*(p+q)+ρ ≤ D.card)
    (hold : ∀ s, missingNeighbors G D (φ (Sum.inl s)) ≤ p+s.val+1+r s)
    (hnew : ∀ v, missingNeighbors G D (φ (Sum.inr v)) ≤ (p+q)+2*p+ρ) :
    ∃ M : WeakCliqueImmersion (p+q) G,
      ∀ i, 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*(p+q) := by
  by_cases hlarge : 3*(p+q) < 4*p
  · exact budgeted_model_of_large_carrier G D φ hout hq ht heven hlarge ρ r hr hD hold hnew
  · let E : Fin (p+q) ≃ (Fin p ⊕ Fin q) := finSumFinEquiv.symm
    let C := CarrierPreparation.newSet E
    let ψ := E.toEmbedding.trans φ
    obtain ⟨M⟩ := strong_model_of_small_carrier G C D ψ (by omega)
      (by dsimp [C]; rw [CarrierPreparation.newSet_card]; omega) hρ (by omega) hD
      (fun v => hout (E v)) (by
        intro v hv
        change missingNeighbors G D (φ (E v)) ≤ 2*p+ρ
        cases he : E v with
        | inl s =>
          have hs := hold s
          have hsρ := hrρ s
          have hsp := s.isLt
          omega
        | inr w =>
          exact False.elim (hv ((CarrierPreparation.mem_newSet E v).mpr ⟨w,he⟩))) (by
        intro v hv
        obtain ⟨w,hw⟩ := (CarrierPreparation.mem_newSet E v).mp hv
        change missingNeighbors G D (φ (E v)) ≤ (p+q)+2*p+ρ
        rw [hw]
        exact hnew w)
    refine ⟨M.toWeak,fun i => ?_⟩
    change 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*(p+q)
    rw [M.branch_used_edges]
    omega

end
end Cycle13
