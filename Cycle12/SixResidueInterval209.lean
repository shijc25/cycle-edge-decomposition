import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval209
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩]⟩,
  ⟨{1},9,.long ⟨0,[1,2,10,5,4,3]⟩⟩,
  ⟨{4},9,.long ⟨0,[1,4,3,2,10,5]⟩⟩,
  ⟨{2,3},9,.long ⟨0,[1,3,2,10,5,4]⟩⟩,
  ⟨{2,5},9,.long ⟨0,[1,5,10,2,3,4]⟩⟩,
  ⟨{3,6},9,.long ⟨0,[1,3,4,2,10,5]⟩⟩,
  ⟨{0,3},9,.long ⟨0,[1,3,4,5,10,2]⟩⟩,
  ⟨{2,8},9,.long ⟨0,[1,2,10,5,3,4]⟩⟩,
  ⟨{0,5,6,7,8},6,.pack [⟨0,[2,1,5]⟩,⟨2,[3,5]⟩,⟨2,[4,5,10]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 209) sixResidueChord (sixResidueActiveAt 209).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval209
