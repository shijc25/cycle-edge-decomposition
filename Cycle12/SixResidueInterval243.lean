import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval243
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},7,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[6,2,8,4,12]⟩]⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,12]⟩⟩,
  ⟨{3,7},9,.long ⟨0,[1,3,2,5,4,12]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 243) sixResidueChord (sixResidueActiveAt 243).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval243
