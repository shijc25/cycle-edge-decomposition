import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval034
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{2},9,.long ⟨0,[1,2,3,8,5,4]⟩⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,2,6]⟩⟩,
  ⟨{},3,.pack [⟨0,[1,2,6]⟩,⟨0,[14,3,15]⟩,⟨3,[4,5,8]⟩]⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,8,5]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,2,5,4,3,14]⟩⟩,
  ⟨{3},9,.long ⟨0,[5,4,3,1,2,6]⟩⟩,
  ⟨{0,4},9,.long ⟨0,[1,4,5,8,3,2]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 34) sixResidueChord (sixResidueActiveAt 34).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval034
