import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval246
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},6,.pack [⟨0,[5,4,3,2,6]⟩,⟨0,[10,4,8,2,12]⟩]⟩,
  ⟨{3},9,.long ⟨0,[1,3,2,8,4,5]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,10]⟩⟩,
  ⟨{5,7},9,.long ⟨0,[1,5,2,3,4,10]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 246) sixResidueChord (sixResidueActiveAt 246).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval246
