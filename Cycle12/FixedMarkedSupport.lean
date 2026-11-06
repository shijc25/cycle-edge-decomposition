import Cycle12.FixedMarkedExperiment

namespace Cycle12
open Finset Cycle13
noncomputable section
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

theorem fixed_marked_experiment_support (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (x : Finset V×(Finset V×Ξ))
    (hx : 0 < (fixedMarkedExperiment D N t kap).mass x) :
    x.1⊆D ∧ x.1.card=N ∧ x.2.1⊆x.1 ∧ x.2.1.card=t ∧ 0 < (kap x.2.1).mass x.2.2 := by
  change 0 < (fixedSizeLaw D N).mass x.1*
    ((fixedSizeLaw x.1 t).mass x.2.1*(kap x.2.1).mass x.2.2) at hx
  have hnon₁ := (fixedSizeLaw D N).nonneg x.1
  have hnon₂ := (fixedSizeLaw x.1 t).nonneg x.2.1
  rcases mul_pos_iff.mp hx with ⟨hU,hrest⟩ | ⟨hU,_⟩
  · rcases mul_pos_iff.mp hrest with ⟨hT,hxi⟩ | ⟨hT,_⟩
    · obtain ⟨hUD,hcard⟩ := fixed_size_support D x.1 hN hU
      obtain ⟨hTU,htcard⟩ := fixed_size_support x.1 x.2.1 (by omega : t ≤ x.1.card) hT
      exact ⟨hUD,hcard,hTU,htcard,hxi⟩
    · linarith
  · linarith

end
end Cycle12
