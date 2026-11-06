import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval180
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩]⟩,
  ⟨{0},9,.long ⟨0,[2,1,6,3,4,5]⟩⟩,
  ⟨{6},9,.long ⟨0,[1,6,3,2,4,5]⟩⟩,
  ⟨{2,7},9,.long ⟨0,[1,6,3,2,5,4]⟩⟩,
  ⟨{5,8},7,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[5,3,6]⟩]⟩,
  ⟨{1,2,4},8,.pack [⟨0,[1,2,3,4]⟩,⟨0,[3,6,1,4,5]⟩]⟩,
  ⟨{1,3,5,7},7,.pack [⟨0,[3,1,2,5]⟩,⟨1,[5,4,3,6]⟩]⟩,
  ⟨{1,3,4,7,8},7,.pack [⟨0,[3,1,2,5]⟩,⟨1,[4,5,3,6]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 180) sixResidueChord (sixResidueActiveAt 180).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval180
