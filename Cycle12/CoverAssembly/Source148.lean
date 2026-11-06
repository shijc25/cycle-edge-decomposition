import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0443
import Cycle12.RoutedCases.Batch0444

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source148

def strip0 : RatCoverRectangle := ⟨(519/8000),(1039/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0443.certificate8870.rectangle,RoutedCases.Batch0443.certificate8871.rectangle,RoutedCases.Batch0443.certificate8873.rectangle,RoutedCases.Batch0443.certificate8875.rectangle,RoutedCases.Batch0443.certificate8877.rectangle,RoutedCases.Batch0443.certificate8879.rectangle,RoutedCases.Batch0444.certificate8880.rectangle,RoutedCases.Batch0444.certificate8881.rectangle,RoutedCases.Batch0444.certificate8882.rectangle,RoutedCases.Batch0444.certificate8883.rectangle,RoutedCases.Batch0444.certificate8884.rectangle,RoutedCases.Batch0444.certificate8885.rectangle,RoutedCases.Batch0444.certificate8886.rectangle,RoutedCases.Batch0444.certificate8887.rectangle,RoutedCases.Batch0444.certificate8888.rectangle,RoutedCases.Batch0444.certificate8889.rectangle,RoutedCases.Batch0444.certificate8890.rectangle,RoutedCases.Batch0444.certificate8891.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8871,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8873,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8880,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8883,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8889,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8891,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1039/16000),(13/200),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0443.certificate8872.rectangle,RoutedCases.Batch0443.certificate8874.rectangle,RoutedCases.Batch0443.certificate8876.rectangle,RoutedCases.Batch0443.certificate8878.rectangle,RoutedCases.Batch0443.certificate8879.rectangle,RoutedCases.Batch0444.certificate8880.rectangle,RoutedCases.Batch0444.certificate8881.rectangle,RoutedCases.Batch0444.certificate8882.rectangle,RoutedCases.Batch0444.certificate8883.rectangle,RoutedCases.Batch0444.certificate8884.rectangle,RoutedCases.Batch0444.certificate8885.rectangle,RoutedCases.Batch0444.certificate8886.rectangle,RoutedCases.Batch0444.certificate8887.rectangle,RoutedCases.Batch0444.certificate8888.rectangle,RoutedCases.Batch0444.certificate8889.rectangle,RoutedCases.Batch0444.certificate8890.rectangle,RoutedCases.Batch0444.certificate8891.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8872,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8874,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8878,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8880,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8883,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8889,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8891,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(519/8000),(13/200),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source148
