import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0444
import Cycle12.RoutedCases.Batch0445

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source149

def strip0 : RatCoverRectangle := ⟨(13/200),(1041/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0444.certificate8892.rectangle,RoutedCases.Batch0444.certificate8893.rectangle,RoutedCases.Batch0444.certificate8895.rectangle,RoutedCases.Batch0444.certificate8897.rectangle,RoutedCases.Batch0444.certificate8899.rectangle,RoutedCases.Batch0445.certificate8901.rectangle,RoutedCases.Batch0445.certificate8902.rectangle,RoutedCases.Batch0445.certificate8903.rectangle,RoutedCases.Batch0445.certificate8904.rectangle,RoutedCases.Batch0445.certificate8905.rectangle,RoutedCases.Batch0445.certificate8906.rectangle,RoutedCases.Batch0445.certificate8907.rectangle,RoutedCases.Batch0445.certificate8908.rectangle,RoutedCases.Batch0445.certificate8909.rectangle,RoutedCases.Batch0445.certificate8910.rectangle,RoutedCases.Batch0445.certificate8911.rectangle,RoutedCases.Batch0445.certificate8912.rectangle,RoutedCases.Batch0445.certificate8913.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8892,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8893,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8895,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8897,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8899,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8901,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8902,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8903,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8904,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8905,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8906,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8907,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8908,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8909,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8910,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8911,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8912,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8913,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1041/16000),(521/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0444.certificate8894.rectangle,RoutedCases.Batch0444.certificate8896.rectangle,RoutedCases.Batch0444.certificate8898.rectangle,RoutedCases.Batch0445.certificate8900.rectangle,RoutedCases.Batch0445.certificate8901.rectangle,RoutedCases.Batch0445.certificate8902.rectangle,RoutedCases.Batch0445.certificate8903.rectangle,RoutedCases.Batch0445.certificate8904.rectangle,RoutedCases.Batch0445.certificate8905.rectangle,RoutedCases.Batch0445.certificate8906.rectangle,RoutedCases.Batch0445.certificate8907.rectangle,RoutedCases.Batch0445.certificate8908.rectangle,RoutedCases.Batch0445.certificate8909.rectangle,RoutedCases.Batch0445.certificate8910.rectangle,RoutedCases.Batch0445.certificate8911.rectangle,RoutedCases.Batch0445.certificate8912.rectangle,RoutedCases.Batch0445.certificate8913.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8894,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8896,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0444.sound8898,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8900,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8901,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8902,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8903,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8904,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8905,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8906,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8907,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8908,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8909,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8910,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8911,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8912,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8913,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/200),(521/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source149
