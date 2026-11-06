import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval226
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{},4,.pack [⟨0,[1,2,3,4,5]⟩,⟨2,[12,4,13]⟩]⟩,
  ⟨{3},9,.long ⟨0,[1,3,2,12,4,5]⟩⟩,
  ⟨{5},9,.long ⟨0,[1,5,4,3,2,12]⟩⟩,
  ⟨{8},9,.long ⟨0,[1,2,3,5,4,12]⟩⟩,
  ⟨{0,2,4,6},6,.pack [⟨0,[2,1,4]⟩,⟨0,[5,4,2,12]⟩,⟨2,[3,4,13]⟩]⟩,
  ⟨{2,4,7},5,.pack [⟨0,[4,1,2,5]⟩,⟨0,[12,2,3,4,13]⟩]⟩,
  ⟨{0,2,6,7},6,.pack [⟨0,[1,2]⟩,⟨0,[4,2,5]⟩,⟨0,[12,2,3,4,13]⟩]⟩,
  ⟨{1,4,6},5,.pack [⟨0,[3,2,1,4,5]⟩,⟨0,[12,2,4,13]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 226) sixResidueChord (sixResidueActiveAt 226).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval226
