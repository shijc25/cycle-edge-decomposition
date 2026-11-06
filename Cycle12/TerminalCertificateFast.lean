import Cycle12.TerminalCertificate

/-! A smaller decidable instance: inspect only the explicitly listed edges
when ruling out loops. This changes evaluation cost, not the proposition. -/
namespace Cycle12.TerminalCert
variable {V : Type} [Fintype V] [DecidableEq V]

instance (priority := 2000) fastValidDecidable {d : ℕ}
    (E : Finset (Sym2 V)) (words : Fin d → CycleWord V) : Decidable (Valid E words) := by
  letI : Decidable (∀ e ∈ E, ¬e.IsDiag) := Finset.decidableDforallFinset
  unfold Valid Pairwise
  infer_instance

end Cycle12.TerminalCert
