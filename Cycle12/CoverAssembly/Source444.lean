import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch000
import Cycle12.RoutedCases.Batch0935
import Cycle12.RoutedCases.Batch0936

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source444

def strip0 : RatCoverRectangle := ⟨(4/125),(33/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0935.certificate18711.rectangle,RoutedCases.Batch0935.certificate18712.rectangle,RoutedCases.Batch0935.certificate18713.rectangle,RoutedCases.Batch0935.certificate18714.rectangle,RoutedCases.Batch0935.certificate18715.rectangle,RoutedCases.Batch0935.certificate18716.rectangle,RoutedCases.Batch0935.certificate18717.rectangle,RoutedCases.Batch0935.certificate18718.rectangle,RoutedCases.Batch0935.certificate18719.rectangle,RoutedCases.Batch0935.certificate18720.rectangle,RoutedCases.Batch0935.certificate18721.rectangle,RoutedCases.Batch0935.certificate18722.rectangle,RoutedCases.Batch0935.certificate18723.rectangle,RoutedCases.Batch0935.certificate18724.rectangle,RoutedCases.Batch0935.certificate18725.rectangle,RoutedCases.Batch0935.certificate18726.rectangle,RoutedCases.Batch0936.certificate18727.rectangle,RoutedCases.Batch0936.certificate18728.rectangle,RoutedCases.Batch0936.certificate18729.rectangle,RoutedCases.Batch0936.certificate18730.rectangle,RoutedCases.Batch0936.certificate18731.rectangle,RoutedCases.Batch0936.certificate18732.rectangle,RoutedCases.Batch0936.certificate18733.rectangle,RoutedCases.Batch0936.certificate18734.rectangle,RoutedCases.Batch0936.certificate18735.rectangle,RoutedCases.Batch0936.certificate18736.rectangle,RoutedCases.Batch0936.certificate18737.rectangle,RoutedCases.Batch0936.certificate18738.rectangle,RoutedCases.Batch0936.certificate18739.rectangle,RoutedCases.Batch0936.certificate18740.rectangle,RoutedCases.Batch0936.certificate18741.rectangle,DirectCases.Batch000.certificate18742.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18711,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18716,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18717,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18718,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18719,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18720,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18721,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18722,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18723,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18724,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18725,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0935.sound18726,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18727,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18728,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18729,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18738,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18739,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0936.sound18741,List.forall_mem_cons.mpr ⟨DirectCases.Batch000.sound18742,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(4/125),(33/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source444
