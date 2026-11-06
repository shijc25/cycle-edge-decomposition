import Cycle12.SixResidueModels

namespace Cycle12
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 32000000

def sixResidueParameterIndex (t : Fin 14) (counts : Fin 4 → Fin 3) (ear : Fin 5) : Fin 272 :=
  Fin.ofNat 272 (if t.val<4 then t.val*40+(4*(counts 0).val+2*(counts 1).val+(counts 2).val)*5+ear.val
    else if t.val<12 then 160+(t.val-4)*8+4*(counts 0).val+2*(counts 1).val+(counts 2).val
    else 224+(t.val-12)*24+(4*(counts 0).val+2*(counts 1).val+(counts 2).val)*3+(counts 3).val)

/-- The finite catalogue covers every valid combination of attachment
multiplicities and optional exterior edge, with an explicit inverse index. -/
theorem six_residue_parameter_coverage : ∀ t counts ear,
    SixResidueParametersValid t counts ear →
      sixResidueParameters (sixResidueParameterIndex t counts ear)=(t,counts,ear) := by
  decide +kernel

theorem six_residue_slot_cover : ∀ t : Fin 14, ∀ i∈sixAttachmentFamily t,
    ∃ j : Fin 4, sixResidueSlot t j=some i := by decide +kernel

theorem six_residue_slot_injective : ∀ t : Fin 14, ∀ i : Fin 11,
    ∀ j k : Fin 4, sixResidueSlot t j=some i → sixResidueSlot t k=some i → j=k := by
  decide +kernel

theorem six_residue_slot_in_family : ∀ t : Fin 14, ∀ j : Fin 4, ∀ i : Fin 11,
    sixResidueSlot t j=some i → i∈sixAttachmentFamily t := by decide +kernel

end Cycle12
