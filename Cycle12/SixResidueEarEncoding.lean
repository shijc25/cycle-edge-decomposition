import Cycle12.SixResidueModels

namespace Cycle12
open SimpleGraph Finset

def sixResidueEarChoice (a b : Bool) : Fin 5 :=
  if a then (if b then 4 else 2) else (if b then 3 else 1)

theorem six_residue_ear_choice_nonzero : ∀ a b, sixResidueEarChoice a b≠0 := by decide +kernel

theorem six_residue_ear_choice_edges : ∀ a b,
    sixResidueEar (sixResidueEarChoice a b)=
      ({s(0,14),s(14,15),s(3,15)} ∪ (if a then {s(3,14)} else ∅)) ∪
        (if b then {s(0,15)} else ∅) := by decide +kernel

theorem six_residue_ear_choice_members : ∀ a b,
    s(14,15)∈sixResidueEar (sixResidueEarChoice a b) ∧
    s(14,0)∈sixResidueEar (sixResidueEarChoice a b) ∧
    s(15,3)∈sixResidueEar (sixResidueEarChoice a b) ∧
    (a=true → s(14,3)∈sixResidueEar (sixResidueEarChoice a b)) ∧
    (b=true → s(15,0)∈sixResidueEar (sixResidueEarChoice a b)) := by decide +kernel

end Cycle12
