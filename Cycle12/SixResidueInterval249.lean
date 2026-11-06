import Cycle12.SixResidueModels

namespace Cycle12.SixResidueInterval249
open SimpleGraph Finset TerminalCert
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

def data : List (ChordCertificate (Fin 9) (Fin 16)) := [
  ⟨{2},9,.long ⟨0,[1,2,3,12,5,4]⟩⟩,
  ⟨{0},9,.long ⟨0,[1,12,5,4,3,2]⟩⟩,
  ⟨{},3,.pack [⟨1,[2,3,4,5,12]⟩]⟩,
  ⟨{6},9,.long ⟨0,[1,2,4,3,12,5]⟩⟩,
  ⟨{3,5},6,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[3,12,5]⟩]⟩,
  ⟨{3,8},6,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[3,5,12]⟩]⟩,
  ⟨{5,8},6,.pack [⟨0,[1,2,3,4,5]⟩,⟨1,[5,3,12]⟩]⟩,
  ⟨{1,3,7},4,.pack [⟨0,[3,1,2,5]⟩,⟨3,[4,5,12]⟩]⟩,
  ⟨{1,4,5},4,.pack [⟨0,[3,2,1,4,5]⟩,⟨1,[5,12]⟩]⟩,
  ⟨{1,4,8},4,.pack [⟨0,[3,2,1,4,5]⟩,⟨3,[5,12]⟩]⟩
]

theorem witnesses_checked : ∀ i : Fin data.length, (data.get i).Checks
    (sixResidueBaseAt 249) sixResidueChord (sixResidueActiveAt 249).card := by decide +kernel

theorem all_chords_covered : ∀ S : Finset (Fin 9),
    ∃ i : Fin data.length, (data.get i).Accepts S := by decide +kernel

end Cycle12.SixResidueInterval249
