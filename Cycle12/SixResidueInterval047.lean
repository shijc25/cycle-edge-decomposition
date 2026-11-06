import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval047
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},6,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[10,3,15,14]⟩]⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,15,14]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,2,5,4,3,10]⟩⟩,
  ⟨{4,8},9,.long ⟨0,[1,4,5,3,15,14]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 47) sixResidueChord (sixResidueActiveAt 47).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval047
