import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0791
import Cycle12.RoutedCases.Batch0792

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source301

def strip0 : RatCoverRectangle := ⟨(7/125),(449/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0791.certificate15829.rectangle,RoutedCases.Batch0791.certificate15830.rectangle,RoutedCases.Batch0791.certificate15831.rectangle,RoutedCases.Batch0791.certificate15832.rectangle,RoutedCases.Batch0791.certificate15833.rectangle,RoutedCases.Batch0791.certificate15834.rectangle,RoutedCases.Batch0791.certificate15835.rectangle,RoutedCases.Batch0791.certificate15836.rectangle,RoutedCases.Batch0791.certificate15838.rectangle,RoutedCases.Batch0792.certificate15840.rectangle,RoutedCases.Batch0792.certificate15841.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15836,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15841,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(449/8000),(9/160),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0791.certificate15829.rectangle,RoutedCases.Batch0791.certificate15830.rectangle,RoutedCases.Batch0791.certificate15831.rectangle,RoutedCases.Batch0791.certificate15832.rectangle,RoutedCases.Batch0791.certificate15833.rectangle,RoutedCases.Batch0791.certificate15834.rectangle,RoutedCases.Batch0791.certificate15835.rectangle,RoutedCases.Batch0791.certificate15836.rectangle,RoutedCases.Batch0791.certificate15838.rectangle,RoutedCases.Batch0792.certificate15840.rectangle,RoutedCases.Batch0792.certificate15842.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15836,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15842,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(9/160),(113/2000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0791.certificate15829.rectangle,RoutedCases.Batch0791.certificate15830.rectangle,RoutedCases.Batch0791.certificate15831.rectangle,RoutedCases.Batch0791.certificate15832.rectangle,RoutedCases.Batch0791.certificate15833.rectangle,RoutedCases.Batch0791.certificate15834.rectangle,RoutedCases.Batch0791.certificate15835.rectangle,RoutedCases.Batch0791.certificate15837.rectangle,RoutedCases.Batch0791.certificate15839.rectangle,RoutedCases.Batch0792.certificate15843.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15837,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0791.sound15839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15843,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/125),(113/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source301
