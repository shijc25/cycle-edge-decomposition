import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval179
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},5,.pack [⟨0,[1,8,5]⟩,⟨1,[2,3,4,10]⟩]⟩,
  ⟨{0},9,.long ⟨0,[1,8,5,4,3,2]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,10,4,3,2,5]⟩⟩,
  ⟨{1,6},9,.long ⟨0,[1,8,5,4,2,3]⟩⟩,
  ⟨{1,2},9,.long ⟨0,[3,2,1,8,5,4]⟩⟩,
  ⟨{2,6,8},9,.long ⟨0,[1,8,5,3,2,4]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 179) sixResidueChord (sixResidueActiveAt 179).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval179
