import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval173
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},5,.pack [⟨0,[1,10,4,5]⟩,⟨2,[3,4,6]⟩]⟩,
  ⟨{3},9,.long ⟨0,[1,3,2,6,4,5]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,10,4,3,2,5]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,6,4,3,5]⟩⟩,
  ⟨{1,5},9,.long ⟨0,[1,5,4,6,2,3]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 173) sixResidueChord (sixResidueActiveAt 173).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval173
