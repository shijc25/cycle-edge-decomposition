import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval210
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨1,[2,3,4,5,8]⟩]⟩,
  ⟨{0},9,.long ⟨0,[1,8,5,4,3,2]⟩⟩,
  ⟨{2},9,.long ⟨0,[4,3,2,1,8,5]⟩⟩,
  ⟨{1,6},9,.long ⟨0,[1,8,5,4,2,3]⟩⟩,
  ⟨{3,8},7,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[3,5,8]⟩]⟩,
  ⟨{4,6,7},8,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[4,2,5,8]⟩]⟩,
  ⟨{1,3,4,5,7},7,.pack [⟨0,[3,1,5]⟩,⟨1,[4,3,2,5,8]⟩]⟩,
  ⟨{1,4,5,8},7,.pack [⟨0,[3,2,1,5]⟩,⟨1,[4,3,5,8]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 210) sixResidueChord (sixResidueActiveAt 210).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval210
