import Cycle12.TerminalCertificateFast

namespace Cycle12.TerminalCert
open SimpleGraph Finset

/-- Data may supply either a packing or a simple long cycle. The latter
discharges an excluded finite case only when the actual short-cycle
hypothesis is supplied to the soundness theorem. -/
inductive DecisionCertificate (V : Type) where
  | pack (words : List (CycleWord V))
  | long (word : CycleWord V)

instance {V : Type} : Inhabited (DecisionCertificate V) := ⟨.pack []⟩

def DecisionCertificate.Checks {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (certificate : DecisionCertificate V) : Prop :=
  match certificate with
  | .pack words => Valid E words.get ∧
      42*words.length+23*(E\covered words.get).card ≤
        19*(Fintype.card V-1)+6*E.card
  | .long word => word.Valid (graph E) ∧ 7≤word.tail.length+1

instance {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (certificate : DecisionCertificate V) :
    Decidable (certificate.Checks E) := by
  cases certificate <;> unfold DecisionCertificate.Checks <;> infer_instance

theorem DecisionCertificate.sound {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (certificate : DecisionCertificate V)
    (hc : certificate.Checks E) (hshort : Cycle13.NoCycleAtLeast (graph E) 7) :
    ∃ P : Cycle13.CyclePacking (graph E),
      P.cost ≤ 19*(Fintype.card V-1)+6*E.card := by
  cases certificate with
  | pack words => exact TerminalCert.sound E words.get hc.1 hc.2
  | long word => exact False.elim (long_cycle_excludes E word hc.1 hc.2 hshort)

end Cycle12.TerminalCert
