import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval090
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩]⟩,
  ⟨{5},9,.long ⟨0,[5,1,2,3,4,8]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,8]⟩⟩,
  ⟨{3,7},9,.long ⟨0,[1,3,2,5,4,8]⟩⟩,
  ⟨{0,1,4,6},7,.pack [⟨0,[2,1,4,5]⟩,⟨0,[3,2,4,8]⟩]⟩,
  ⟨{2,6,7},7,.pack [⟨0,[1,2,3,4]⟩,⟨0,[5,2,4,8]⟩]⟩,
  ⟨{1,3,4},8,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[3,1,4,8]⟩]⟩,
  ⟨{0,1,3,6},8,.pack [⟨0,[2,1,3,4,5]⟩,⟨0,[3,2,4,8]⟩]⟩,
  ⟨{0,3,4,6},8,.pack [⟨0,[1,2,4,5]⟩,⟨0,[2,3,1,4,8]⟩]⟩,
  ⟨{0,2,4,7},7,.pack [⟨0,[2,1,4]⟩,⟨0,[5,2,3,4,8]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 90) sixResidueChord (sixResidueActiveAt 90).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval090
