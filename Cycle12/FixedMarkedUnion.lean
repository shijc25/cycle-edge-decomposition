import Cycle12.FixedMarkedExperiment

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

/-- Reversal and the union bound over all marked labels. Choices of a
truncation cap may depend on T, its label, and xi, but not on the residual
sample. No extra union factor is paid for deterministic bins of these data. -/
theorem fixed_marked_uniform_label_bound (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (E : Finset V → Finset V → Ξ → Finset V → Prop) {eta : ℝ}
    (hpoint : ∀ T⊆D, T.card=t → ∀ xi A, A⊆T →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => E (T∪R) T xi A) ≤ eta) :
    (fixedMarkedExperiment D N t kap).prob
      (fun x => ∃ A⊆x.2.1, E x.1 x.2.1 x.2.2 A) ≤ (2:ℝ)^t*eta := by
  rw [fixed_marked_experiment_prob D N t kap
    (fun U T xi => ∃ A⊆T, E U T xi A),fixed_marked_sampling_order_reversal D hN ht]
  rw [← (fixedSizeLaw D t).expect_const ((2:ℝ)^t*eta)]
  apply FiniteLaw.expect_mono_support
  intro T hT
  obtain ⟨hTD,hcard⟩ := fixed_size_support D T (ht.trans hN) hT
  unfold FiniteLaw.prob
  rw [FiniteLaw.expect_comm]
  change (kap T).expect (fun xi => (fixedSizeLaw (D\T) (N-t)).prob
    (fun R => ∃ A⊆T, E (T∪R) T xi A)) ≤ _
  have hp (xi : Ξ) : (fixedSizeLaw (D\T) (N-t)).prob
      (fun R => ∃ A⊆T, E (T∪R) T xi A) ≤ (2:ℝ)^t*eta := by
    have hu := prob_exists_finset_le_sum (fixedSizeLaw (D\T) (N-t)) T.powerset
      (fun A R => E (T∪R) T xi A)
    simp only [mem_powerset] at hu
    apply hu.trans
    calc
      _ ≤ ∑ _A∈T.powerset, eta := sum_le_sum (fun A hA => hpoint T hTD hcard xi A (mem_powerset.mp hA))
      _ = _ := by simp only [sum_const,card_powerset,hcard,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  simpa only [FiniteLaw.expect_const] using (kap T).expect_mono hp

end
end Cycle12
