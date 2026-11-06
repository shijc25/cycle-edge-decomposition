import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval266
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{2},9,.long ⟨0,[1,2,3,8,5,4]⟩⟩,
  ⟨{0},9,.long ⟨0,[2,1,6,3,4,5]⟩⟩,
  ⟨{},3,.pack [⟨1,[2,3,6]⟩,⟨3,[4,5,8]⟩]⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,8,5]⟩⟩,
  ⟨{5},7,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[5,8,3,6]⟩]⟩,
  ⟨{4,8},7,.pack [⟨0,[1,2,3,5]⟩,⟨1,[4,5,8,3,6]⟩]⟩,
  ⟨{3,7},7,.pack [⟨0,[1,3,4,5]⟩,⟨1,[2,5,8,3,6]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 266) sixResidueChord (sixResidueActiveAt 266).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval266
