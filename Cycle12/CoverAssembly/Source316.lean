import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0807

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source316

def strip0 : RatCoverRectangle := ⟨(251/4000),(63/1000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0807.certificate16145.rectangle,RoutedCases.Batch0807.certificate16146.rectangle,RoutedCases.Batch0807.certificate16147.rectangle,RoutedCases.Batch0807.certificate16148.rectangle,RoutedCases.Batch0807.certificate16149.rectangle,RoutedCases.Batch0807.certificate16150.rectangle,RoutedCases.Batch0807.certificate16151.rectangle,RoutedCases.Batch0807.certificate16152.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16145,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16146,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16147,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16148,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16149,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16150,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16151,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16152,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(251/4000),(63/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source316
