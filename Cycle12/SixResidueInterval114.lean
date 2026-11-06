import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval114
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{3},9,.long ⟨0,[5,4,3,1,2,6]⟩⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,2,6]⟩⟩,
  ⟨{},3,.pack [⟨0,[1,2,6]⟩,⟨0,[5,4,8]⟩,⟨0,[14,3,15]⟩]⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,14,15]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,2,5,4,3,14]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,8]⟩⟩,
  ⟨{0,4},9,.long ⟨0,[2,1,4,3,14,15]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 114) sixResidueChord (sixResidueActiveAt 114).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval114
