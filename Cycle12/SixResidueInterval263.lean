import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval263
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{0},9,.long ⟨0,[1,10,5,4,3,2]⟩⟩,
  ⟨{2},9,.long ⟨0,[4,3,2,1,10,5]⟩⟩,
  ⟨{},3,.pack [⟨0,[1,10,5]⟩,⟨1,[2,3,6]⟩]⟩,
  ⟨{6},9,.long ⟨0,[1,6,3,2,4,5]⟩⟩,
  ⟨{8},7,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[6,3,5,10]⟩]⟩,
  ⟨{1,5},7,.pack [⟨0,[3,2,1,5]⟩,⟨1,[6,3,4,5,10]⟩]⟩,
  ⟨{3,7},7,.pack [⟨0,[1,3,2,5]⟩,⟨1,[6,3,4,5,10]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 263) sixResidueChord (sixResidueActiveAt 263).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval263
