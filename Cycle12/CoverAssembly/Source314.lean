import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0806

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source314

def strip0 : RatCoverRectangle := ⟨(249/4000),(1/16),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0806.certificate16128.rectangle,RoutedCases.Batch0806.certificate16129.rectangle,RoutedCases.Batch0806.certificate16130.rectangle,RoutedCases.Batch0806.certificate16131.rectangle,RoutedCases.Batch0806.certificate16132.rectangle,RoutedCases.Batch0806.certificate16133.rectangle,RoutedCases.Batch0806.certificate16134.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16129,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16131,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16133,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16134,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(249/4000),(1/16),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source314
