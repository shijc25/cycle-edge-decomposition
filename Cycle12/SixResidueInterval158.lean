import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval158
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},5,.pack [⟨0,[5,4,8]⟩,⟨0,[10,3,15,14]⟩,⟨1,[2,3,6]⟩]⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,15,14]⟩⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,15,14]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,2,5,4,3,10]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,8]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 158) sixResidueChord (sixResidueActiveAt 158).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval158
