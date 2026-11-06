import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch000
import Cycle12.RoutedCases.Batch0931
import Cycle12.RoutedCases.Batch0932
import Cycle12.RoutedCases.Batch0933

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source442

def strip0 : RatCoverRectangle := ⟨(3/100),(31/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0931.certificate18644.rectangle,RoutedCases.Batch0932.certificate18645.rectangle,RoutedCases.Batch0932.certificate18646.rectangle,RoutedCases.Batch0932.certificate18647.rectangle,RoutedCases.Batch0932.certificate18648.rectangle,RoutedCases.Batch0932.certificate18649.rectangle,RoutedCases.Batch0932.certificate18650.rectangle,RoutedCases.Batch0932.certificate18651.rectangle,RoutedCases.Batch0932.certificate18652.rectangle,RoutedCases.Batch0932.certificate18653.rectangle,RoutedCases.Batch0932.certificate18654.rectangle,RoutedCases.Batch0932.certificate18655.rectangle,RoutedCases.Batch0932.certificate18656.rectangle,RoutedCases.Batch0932.certificate18657.rectangle,RoutedCases.Batch0932.certificate18658.rectangle,RoutedCases.Batch0932.certificate18659.rectangle,RoutedCases.Batch0932.certificate18660.rectangle,RoutedCases.Batch0932.certificate18661.rectangle,RoutedCases.Batch0932.certificate18662.rectangle,RoutedCases.Batch0932.certificate18663.rectangle,RoutedCases.Batch0932.certificate18664.rectangle,RoutedCases.Batch0933.certificate18665.rectangle,RoutedCases.Batch0933.certificate18666.rectangle,RoutedCases.Batch0933.certificate18667.rectangle,RoutedCases.Batch0933.certificate18668.rectangle,RoutedCases.Batch0933.certificate18669.rectangle,RoutedCases.Batch0933.certificate18670.rectangle,RoutedCases.Batch0933.certificate18671.rectangle,RoutedCases.Batch0933.certificate18672.rectangle,RoutedCases.Batch0933.certificate18673.rectangle,RoutedCases.Batch0933.certificate18674.rectangle,RoutedCases.Batch0933.certificate18675.rectangle,RoutedCases.Batch0933.certificate18676.rectangle,DirectCases.Batch000.certificate18677.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0931.sound18644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18647,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18648,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18649,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18651,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18652,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18653,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18654,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18655,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18656,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18657,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18658,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18659,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18660,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18661,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18662,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18663,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0932.sound18664,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18665,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18666,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18667,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18668,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18669,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18670,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18671,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18672,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18673,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18674,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18675,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0933.sound18676,List.forall_mem_cons.mpr ⟨DirectCases.Batch000.sound18677,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/100),(31/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source442
