import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval100
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[5,4,3,2,6]⟩]⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,2,6]⟩⟩,
  ⟨{3},9,.long ⟨0,[5,4,3,1,2,6]⟩⟩,
  ⟨{2,6},7,.pack [⟨0,[1,2,3,4]⟩,⟨0,[5,4,2,6]⟩]⟩,
  ⟨{1,7,8},8,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[3,5,2,6]⟩]⟩,
  ⟨{0,2,4},7,.pack [⟨0,[2,1,4]⟩,⟨0,[5,4,3,2,6]⟩]⟩,
  ⟨{0,1,4,6},7,.pack [⟨0,[2,1,4,3]⟩,⟨0,[5,4,2,6]⟩]⟩,
  ⟨{4,7,8},9,.long ⟨0,[1,4,3,5,2,6]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 100) sixResidueChord (sixResidueActiveAt 100).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval100
