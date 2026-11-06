import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval244
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},5,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[6,2,12]⟩,⟨2,[8,4,13]⟩]⟩,
  ⟨{3},9,.long ⟨0,[1,3,2,8,4,5]⟩⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,2,6]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,12]⟩⟩,
  ⟨{1,2,4,6,7},8,.pack [⟨0,[3,2,1,4]⟩,⟨0,[5,2,4,12]⟩,⟨0,[6,2,8,4,13]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 244) sixResidueChord (sixResidueActiveAt 244).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval244
