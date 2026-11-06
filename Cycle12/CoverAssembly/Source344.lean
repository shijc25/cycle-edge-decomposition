import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0835

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source344

def strip0 : RatCoverRectangle := ⟨(7/500),(57/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0835.certificate16712.rectangle,RoutedCases.Batch0835.certificate16713.rectangle,RoutedCases.Batch0835.certificate16714.rectangle,RoutedCases.Batch0835.certificate16715.rectangle,RoutedCases.Batch0835.certificate16716.rectangle,RoutedCases.Batch0835.certificate16718.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16716,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16718,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(57/4000),(29/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0835.certificate16712.rectangle,RoutedCases.Batch0835.certificate16713.rectangle,RoutedCases.Batch0835.certificate16714.rectangle,RoutedCases.Batch0835.certificate16715.rectangle,RoutedCases.Batch0835.certificate16717.rectangle,RoutedCases.Batch0835.certificate16719.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16717,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16719,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/500),(29/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source344
