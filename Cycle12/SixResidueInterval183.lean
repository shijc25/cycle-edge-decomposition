import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval183
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨1,[2,3,6]⟩,⟨1,[8,5,4,10]⟩]⟩,
  ⟨{0},9,.long ⟨0,[1,8,5,4,3,2]⟩⟩,
  ⟨{6},9,.long ⟨0,[1,6,3,2,4,5]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,10,4,3,2,5]⟩⟩,
  ⟨{1},9,.long ⟨0,[3,2,1,10,4,5]⟩⟩,
  ⟨{2},9,.long ⟨0,[4,3,2,1,8,5]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 183) sixResidueChord (sixResidueActiveAt 183).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval183
