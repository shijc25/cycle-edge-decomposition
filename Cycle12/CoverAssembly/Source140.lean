import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0434
import Cycle12.RoutedCases.Batch0435

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source140

def strip0 : RatCoverRectangle := ⟨(511/8000),(1023/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0434.certificate8699.rectangle,RoutedCases.Batch0435.certificate8701.rectangle,RoutedCases.Batch0435.certificate8703.rectangle,RoutedCases.Batch0435.certificate8705.rectangle,RoutedCases.Batch0435.certificate8706.rectangle,RoutedCases.Batch0435.certificate8707.rectangle,RoutedCases.Batch0435.certificate8708.rectangle,RoutedCases.Batch0435.certificate8709.rectangle,RoutedCases.Batch0435.certificate8710.rectangle,RoutedCases.Batch0435.certificate8711.rectangle,RoutedCases.Batch0435.certificate8712.rectangle,RoutedCases.Batch0435.certificate8713.rectangle,RoutedCases.Batch0435.certificate8714.rectangle,RoutedCases.Batch0435.certificate8715.rectangle,RoutedCases.Batch0435.certificate8716.rectangle,RoutedCases.Batch0435.certificate8717.rectangle,RoutedCases.Batch0435.certificate8718.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0434.sound8699,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8701,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8703,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8705,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8706,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8707,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8708,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8710,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8711,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8716,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8717,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8718,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1023/16000),(8/125),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0435.certificate8700.rectangle,RoutedCases.Batch0435.certificate8702.rectangle,RoutedCases.Batch0435.certificate8704.rectangle,RoutedCases.Batch0435.certificate8705.rectangle,RoutedCases.Batch0435.certificate8706.rectangle,RoutedCases.Batch0435.certificate8707.rectangle,RoutedCases.Batch0435.certificate8708.rectangle,RoutedCases.Batch0435.certificate8709.rectangle,RoutedCases.Batch0435.certificate8710.rectangle,RoutedCases.Batch0435.certificate8711.rectangle,RoutedCases.Batch0435.certificate8712.rectangle,RoutedCases.Batch0435.certificate8713.rectangle,RoutedCases.Batch0435.certificate8714.rectangle,RoutedCases.Batch0435.certificate8715.rectangle,RoutedCases.Batch0435.certificate8716.rectangle,RoutedCases.Batch0435.certificate8717.rectangle,RoutedCases.Batch0435.certificate8718.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8700,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8702,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8704,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8705,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8706,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8707,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8708,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8710,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8711,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8716,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8717,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8718,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(511/8000),(8/125),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source140
