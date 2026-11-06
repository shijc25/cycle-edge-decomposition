import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0841
import Cycle12.RoutedCases.Batch0842

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source353

def strip0 : RatCoverRectangle := ⟨(1/50),(81/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16839.rectangle,RoutedCases.Batch0842.certificate16840.rectangle,RoutedCases.Batch0842.certificate16841.rectangle,RoutedCases.Batch0842.certificate16842.rectangle,RoutedCases.Batch0842.certificate16844.rectangle,RoutedCases.Batch0842.certificate16848.rectangle,RoutedCases.Batch0842.certificate16850.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16848,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16850,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(81/4000),(41/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16839.rectangle,RoutedCases.Batch0842.certificate16840.rectangle,RoutedCases.Batch0842.certificate16841.rectangle,RoutedCases.Batch0842.certificate16842.rectangle,RoutedCases.Batch0842.certificate16844.rectangle,RoutedCases.Batch0842.certificate16849.rectangle,RoutedCases.Batch0842.certificate16851.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16849,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16851,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(41/2000),(83/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16839.rectangle,RoutedCases.Batch0842.certificate16840.rectangle,RoutedCases.Batch0842.certificate16841.rectangle,RoutedCases.Batch0842.certificate16843.rectangle,RoutedCases.Batch0842.certificate16845.rectangle,RoutedCases.Batch0842.certificate16846.rectangle,RoutedCases.Batch0842.certificate16852.rectangle,RoutedCases.Batch0842.certificate16854.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16846,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16852,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16854,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(83/4000),(167/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16839.rectangle,RoutedCases.Batch0842.certificate16840.rectangle,RoutedCases.Batch0842.certificate16841.rectangle,RoutedCases.Batch0842.certificate16843.rectangle,RoutedCases.Batch0842.certificate16845.rectangle,RoutedCases.Batch0842.certificate16847.rectangle,RoutedCases.Batch0842.certificate16853.rectangle,RoutedCases.Batch0842.certificate16855.rectangle,RoutedCases.Batch0842.certificate16856.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16847,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16853,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16855,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16856,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(167/8000),(21/1000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16839.rectangle,RoutedCases.Batch0842.certificate16840.rectangle,RoutedCases.Batch0842.certificate16841.rectangle,RoutedCases.Batch0842.certificate16843.rectangle,RoutedCases.Batch0842.certificate16845.rectangle,RoutedCases.Batch0842.certificate16847.rectangle,RoutedCases.Batch0842.certificate16853.rectangle,RoutedCases.Batch0842.certificate16855.rectangle,RoutedCases.Batch0842.certificate16857.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16847,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16853,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16855,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0842.sound16857,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/50),(21/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source353
