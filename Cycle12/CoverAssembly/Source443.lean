import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch000
import Cycle12.RoutedCases.Batch0933
import Cycle12.RoutedCases.Batch0934
import Cycle12.RoutedCases.Batch0935

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source443

def strip0 : RatCoverRectangle := ⟨(31/1000),(4/125),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0933.certificate18678.rectangle,RoutedCases.Batch0933.certificate18679.rectangle,RoutedCases.Batch0933.certificate18680.rectangle,RoutedCases.Batch0933.certificate18681.rectangle,RoutedCases.Batch0933.certificate18682.rectangle,RoutedCases.Batch0933.certificate18683.rectangle,RoutedCases.Batch0933.certificate18684.rectangle,RoutedCases.Batch0933.certificate18685.rectangle,RoutedCases.Batch0934.certificate18686.rectangle,RoutedCases.Batch0934.certificate18687.rectangle,RoutedCases.Batch0934.certificate18688.rectangle,RoutedCases.Batch0934.certificate18689.rectangle,RoutedCases.Batch0934.certificate18690.rectangle,RoutedCases.Batch0934.certificate18691.rectangle,RoutedCases.Batch0934.certificate18692.rectangle,RoutedCases.Batch0934.certificate18693.rectangle,RoutedCases.Batch0934.certificate18694.rectangle,RoutedCases.Batch0934.certificate18695.rectangle,RoutedCases.Batch0934.certificate18696.rectangle,RoutedCases.Batch0934.certificate18697.rectangle,RoutedCases.Batch0934.certificate18698.rectangle,RoutedCases.Batch0934.certificate18699.rectangle,RoutedCases.Batch0934.certificate18700.rectangle,RoutedCases.Batch0934.certificate18701.rectangle,RoutedCases.Batch0934.certificate18702.rectangle,RoutedCases.Batch0934.certificate18703.rectangle,RoutedCases.Batch0934.certificate18704.rectangle,RoutedCases.Batch0934.certificate18705.rectangle,RoutedCases.Batch0935.certificate18706.rectangle,RoutedCases.Batch0935.certificate18707.rectangle,RoutedCases.Batch0935.certificate18708.rectangle,RoutedCases.Batch0935.certificate18709.rectangle,DirectCases.Batch000.certificate18710.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18678,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18679,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18680,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18683,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18685,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18687,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18689,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18690,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18691,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18692,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18693,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18694,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18695,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18696,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18697,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18698,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18699,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18700,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18701,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18702,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18703,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18704,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0934.sound18705,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18706,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18707,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18708,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18709,List.forall_mem_cons.mpr ⟨DirectCases.Batch000.sound18710,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(31/1000),(4/125),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source443
