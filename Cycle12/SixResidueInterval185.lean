import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval185
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩]⟩,
  ⟨{1},9,.long ⟨0,[3,2,1,10,4,5]⟩⟩,
  ⟨{7},9,.long ⟨0,[1,10,4,3,2,5]⟩⟩,
  ⟨{0,3},9,.long ⟨0,[2,3,1,10,4,5]⟩⟩,
  ⟨{2,8},9,.long ⟨0,[4,10,1,2,3,5]⟩⟩,
  ⟨{0,5},9,.long ⟨0,[2,3,4,10,1,5]⟩⟩,
  ⟨{2,3,4,5,6},6,.pack [⟨0,[1,2,4]⟩,⟨1,[3,4]⟩,⟨1,[5,4,10]⟩]⟩,
  ⟨{6,8},9,.long ⟨0,[1,10,4,2,3,5]⟩⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 185) sixResidueChord (sixResidueActiveAt 185).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval185
