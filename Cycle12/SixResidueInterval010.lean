import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval010
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩]⟩,
  ⟨{2},9,.long ⟨0,[1,2,3,8,5,4]⟩⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,8,5]⟩⟩,
  ⟨{0,4},9,.long ⟨0,[1,4,5,8,3,2]⟩⟩,
  ⟨{3,5},7,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[3,8,5]⟩]⟩,
  ⟨{0,1,7},8,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[2,5,8,3]⟩]⟩,
  ⟨{3,4,8},7,.pack [⟨0,[1,2,3,5]⟩,⟨1,[3,8,5,4]⟩]⟩,
  ⟨{4,5,8},7,.pack [⟨0,[1,2,3,5]⟩,⟨1,[4,3,8,5]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 10) sixResidueChord (sixResidueActiveAt 10).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval010
