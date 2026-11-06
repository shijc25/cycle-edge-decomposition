import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval172
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩]⟩,
  ⟨{3},9,.long ⟨0,[1,3,2,6,4,5]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,6,4,3,5]⟩⟩,
  ⟨{1,5},9,.long ⟨0,[1,5,4,6,2,3]⟩⟩,
  ⟨{0,2},7,.pack [⟨0,[1,2,3,4]⟩,⟨0,[2,6,4,5]⟩]⟩,
  ⟨{4,5,7},8,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[4,6,2,5]⟩]⟩,
  ⟨{0,1,6},7,.pack [⟨0,[1,2,4,3]⟩,⟨0,[2,6,4,5]⟩]⟩,
  ⟨{1,2,6},7,.pack [⟨0,[1,2,4]⟩,⟨0,[3,2,6,4,5]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 172) sixResidueChord (sixResidueActiveAt 172).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval172
