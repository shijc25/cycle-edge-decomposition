import Cycle12.PhysicalFoldConstructionComplete12

namespace Cycle12

/-- Every finite simple graph has an exact partition into simple cycles
and single original edges with at most twelve times its component rank
many parts. Isolated vertices count as connected components. -/
theorem coefficient12 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ k : ℕ,
    Cycle13.EdgeDecomposition G k ∧ k ≤ 12 * (n - Cycle13.componentCount G) :=
  Global12.coefficient12_from_physical_construction Global12.physical_fold_construction12

end Cycle12
