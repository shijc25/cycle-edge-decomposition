import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval225
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{3},9,.long ⟨0,[1,3,2,12,4,5]⟩⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,2,12]⟩⟩,
  ⟨{},3,.pack [⟨0,[5,4,3,2,12]⟩]⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,12]⟩⟩,
  ⟨{2,6},6,.pack [⟨0,[1,2,3,4]⟩,⟨0,[5,4,2,12]⟩]⟩,
  ⟨{0,6},6,.pack [⟨0,[1,2,3,4,5]⟩,⟨0,[2,4,12]⟩]⟩,
  ⟨{0,2,4},6,.pack [⟨0,[2,1,4]⟩,⟨0,[5,4,3,2,12]⟩]⟩,
  ⟨{0,2,7},6,.pack [⟨0,[1,2,3,4]⟩,⟨0,[2,5,4,12]⟩]⟩,
  ⟨{0,1,4,7},4,.pack [⟨0,[2,1,4,3]⟩,⟨2,[5,4,12]⟩]⟩,
  ⟨{2,4,7},4,.pack [⟨0,[4,1,2,5]⟩,⟨2,[3,4,12]⟩]⟩,
  ⟨{4,6,7},4,.pack [⟨0,[5,2,1,4,12]⟩,⟨2,[3,4]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 225) sixResidueChord (sixResidueActiveAt 225).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval225
