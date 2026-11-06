import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval166
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{0},9,.long ⟨0,[2,1,6,3,4,5]⟩⟩,
  ⟨{5},9,.long ⟨0,[5,1,2,3,4,8]⟩⟩,
  ⟨{},3,.pack [⟨0,[5,4,8]⟩,⟨1,[2,3,6]⟩]⟩,
  ⟨{6},9,.long ⟨0,[1,6,3,2,4,5]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,8]⟩⟩,
  ⟨{1,4},9,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[3,6,1,4,8]⟩]⟩,
  ⟨{3,7},9,.long ⟨0,[1,3,2,5,4,8]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 166) sixResidueChord (sixResidueActiveAt 166).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval166
