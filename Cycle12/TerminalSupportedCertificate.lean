import Cycle12.PackingIsolatedPadding
import Cycle12.TerminalDecisionCertificate

namespace Cycle12.TerminalCert
open SimpleGraph Finset

/-- A finite decision certificate with an explicit budget. The order cost
can therefore count only active vertices in a padded model. -/
def DecisionCertificate.ChecksAt {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (budget : ℕ) (certificate : DecisionCertificate V) : Prop :=
  match certificate with
  | .pack words => Valid E words.get ∧
      42*words.length+23*(E\covered words.get).card ≤ budget
  | .long word => word.Valid (graph E) ∧ 7 ≤ word.tail.length+1

instance {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (budget : ℕ) (certificate : DecisionCertificate V) :
    Decidable (certificate.ChecksAt E budget) := by
  cases certificate <;> unfold DecisionCertificate.ChecksAt <;> infer_instance

theorem DecisionCertificate.soundAt {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (budget : ℕ) (certificate : DecisionCertificate V)
    (hc : certificate.ChecksAt E budget) (hshort : Cycle13.NoCycleAtLeast (graph E) 7) :
    ∃ P : Cycle13.CyclePacking (graph E), P.cost ≤ budget := by
  cases certificate with
  | pack words => exact TerminalCert.sound E words.get hc.1 hc.2
  | long word => exact False.elim (long_cycle_excludes E word hc.1 hc.2 hshort)

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A certificate in a fixed ambient type yields the exact affine bound
on the active induced graph. Isolated slots incur no order or edge cost. -/
theorem DecisionCertificate.soundSupported {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (S : Finset V) (certificate : DecisionCertificate V)
    (hE : ∀ e∈E, ¬e.IsDiag)
    (hS : ∀ x y, (graph E).Adj x y → x∈S ∧ y∈S)
    (hc : certificate.ChecksAt E (19*(S.card-1)+6*E.card))
    (hshort : Cycle13.NoCycleAtLeast ((graph E).induce (S:Set V)) 7) :
    ∃ P : Cycle13.CyclePacking ((graph E).induce (S:Set V)),
      P.cost ≤ 19*(Fintype.card (S:Set V)-1)+
        6*((graph E).induce (S:Set V)).edgeSet.ncard := by
  have hshort' := noLongCycle_of_incident_support (graph E) (S:Set V) hS hshort
  obtain ⟨P,hP⟩ := certificate.soundAt E _ hc hshort'
  refine ⟨P.restrictSupported (S:Set V) hS,?_⟩
  rw [Cycle13.CyclePacking.cost_restrictSupported,
    edge_ncard_induce_of_incident_support (graph E) (S:Set V) hS,
    edgeSet_graph E hE,Set.ncard_coe_finset]
  have hn : Fintype.card (S:Set V)=S.card := Fintype.card_coe S
  rwa [hn]

end
end Cycle12.TerminalCert
