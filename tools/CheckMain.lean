import Cycle12
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ k : ℕ,
    Cycle13.EdgeDecomposition G k ∧ k ≤ 12*(n-Cycle13.componentCount G) :=
  Cycle12.coefficient12
#print axioms Cycle12.coefficient12
