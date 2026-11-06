import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval175
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[5,4,8]⟩,⟨1,[2,3,4,10]⟩]⟩,
  ⟨{3},9,.long ⟨0,[1,3,2,6,4,5]⟩⟩,
  ⟨{1},9,.long ⟨0,[1,10,4,6,2,3]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,10,4,3,2,5]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,8]⟩⟩,
  ⟨{0,5},9,.long ⟨0,[2,3,4,10,1,5]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 175) sixResidueChord (sixResidueActiveAt 175).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval175
