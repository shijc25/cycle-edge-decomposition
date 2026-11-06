import Cycle12.Foundations.Definitions
import OAI.Combinatorics.CycleDecomposition.Main

/-! Compatibility with the pinned OpenAI formalization. The existential bound
below does not establish the explicit coefficient-13 target. -/
namespace Cycle13

theorem edgeDecomposition_iff_openai {V : Type} (G : SimpleGraph V) (k : ℕ) :
    EdgeDecomposition G k ↔ OAI.ErdosGallai.EdgeDecomposition G k := Iff.rfl

theorem single_edge_decomposition {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (Nat.card G.edgeSet) :=
  OAI.ErdosGallai.edgeDecomposition_singleEdges G

/-- A recompiled baseline; the value of `C` is not fixed to 13. -/
theorem known_linear_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ k : ℕ, EdgeDecomposition G k ∧ (k : ℝ) ≤ C * n :=
  OAI.ErdosGallai.erdos_gallai

end Cycle13
