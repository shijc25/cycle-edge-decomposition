import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval190
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{3},9,.long ⟨0,[1,3,2,6,4,5]⟩⟩,
  ⟨{0},9,.long ⟨0,[1,8,5,4,3,2]⟩⟩,
  ⟨{},3,.pack [⟨0,[1,8,5]⟩,⟨2,[3,4,6]⟩]⟩,
  ⟨{2},9,.long ⟨0,[4,3,2,1,8,5]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,6,4,3,5]⟩⟩,
  ⟨{1,5},9,.long ⟨0,[1,5,4,6,2,3]⟩⟩,
  ⟨{4,7},9,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[4,6,2,5,8]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 190) sixResidueChord (sixResidueActiveAt 190).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval190
