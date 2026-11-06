import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval256
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},6,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[12,3,8,5,13]⟩]⟩,
  ⟨{2},9,.long ⟨0,[1,2,3,8,5,4]⟩⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,8,5]⟩⟩,
  ⟨{0,4,7},9,.long ⟨0,[1,4,3,8,5,2]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 256) sixResidueChord (sixResidueActiveAt 256).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval256
