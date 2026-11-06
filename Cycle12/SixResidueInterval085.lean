import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval085
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩]⟩,
  ⟨{4},9,.long ⟨0,[5,4,1,2,3,10]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,2,5,4,3,10]⟩⟩,
  ⟨{0,5},9,.long ⟨0,[2,1,5,4,3,10]⟩⟩,
  ⟨{3,6},9,.long ⟨0,[5,4,2,1,3,10]⟩⟩,
  ⟨{2,5},9,.long ⟨0,[4,5,1,2,3,10]⟩⟩,
  ⟨{0,1,2,3,8},6,.pack [⟨0,[1,3]⟩,⟨0,[2,3,4]⟩,⟨0,[5,3,10]⟩]⟩,
  ⟨{6,8},9,.long ⟨0,[1,2,4,5,3,10]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 85) sixResidueChord (sixResidueActiveAt 85).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval085
