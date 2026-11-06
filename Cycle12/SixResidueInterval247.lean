import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval247
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},7,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[6,2,8,4,10]⟩,⟨2,[12,4,13]⟩]⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,10]⟩⟩,
  ⟨{3,7},9,.long ⟨0,[1,3,2,5,4,10]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 247) sixResidueChord (sixResidueActiveAt 247).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval247
