import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval231
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},5,.pack [⟨0,[1,2,3,4,5]⟩,⟨2,[8,4,12]⟩]⟩,
  ⟨{3},9,.long ⟨0,[1,3,2,8,4,5]⟩⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,2,12]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,12]⟩⟩,
  ⟨{0,2,4,6,7},7,.pack [⟨0,[2,1,4]⟩,⟨0,[5,2,3,4,12]⟩,⟨2,[4,8]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 231) sixResidueChord (sixResidueActiveAt 231).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval231
