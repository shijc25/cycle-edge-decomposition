import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval261
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},5,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[6,3,12]⟩]⟩,
  ⟨{2},9,.long ⟨0,[1,2,3,12,5,4]⟩⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,12,5]⟩⟩,
  ⟨{0,4},9,.long ⟨0,[1,4,5,12,3,2]⟩⟩,
  ⟨{1,3,5,7,8},7,.pack [⟨0,[3,1,2,5]⟩,⟨1,[5,3,6]⟩,⟨3,[4,5,12]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 261) sixResidueChord (sixResidueActiveAt 261).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval261
