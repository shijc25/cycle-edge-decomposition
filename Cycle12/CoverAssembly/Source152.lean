import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0447
import Cycle12.RoutedCases.Batch0448

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source152

def strip0 : RatCoverRectangle := ⟨(523/8000),(1047/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0447.certificate8958.rectangle,RoutedCases.Batch0447.certificate8959.rectangle,RoutedCases.Batch0448.certificate8961.rectangle,RoutedCases.Batch0448.certificate8963.rectangle,RoutedCases.Batch0448.certificate8965.rectangle,RoutedCases.Batch0448.certificate8967.rectangle,RoutedCases.Batch0448.certificate8968.rectangle,RoutedCases.Batch0448.certificate8969.rectangle,RoutedCases.Batch0448.certificate8970.rectangle,RoutedCases.Batch0448.certificate8971.rectangle,RoutedCases.Batch0448.certificate8972.rectangle,RoutedCases.Batch0448.certificate8973.rectangle,RoutedCases.Batch0448.certificate8974.rectangle,RoutedCases.Batch0448.certificate8975.rectangle,RoutedCases.Batch0448.certificate8976.rectangle,RoutedCases.Batch0448.certificate8977.rectangle,RoutedCases.Batch0448.certificate8978.rectangle,RoutedCases.Batch0448.certificate8979.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8958,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8959,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8961,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8963,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8968,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8970,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8971,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8972,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8974,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8975,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8976,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8977,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8978,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8979,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1047/16000),(131/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0448.certificate8960.rectangle,RoutedCases.Batch0448.certificate8962.rectangle,RoutedCases.Batch0448.certificate8964.rectangle,RoutedCases.Batch0448.certificate8966.rectangle,RoutedCases.Batch0448.certificate8967.rectangle,RoutedCases.Batch0448.certificate8968.rectangle,RoutedCases.Batch0448.certificate8969.rectangle,RoutedCases.Batch0448.certificate8970.rectangle,RoutedCases.Batch0448.certificate8971.rectangle,RoutedCases.Batch0448.certificate8972.rectangle,RoutedCases.Batch0448.certificate8973.rectangle,RoutedCases.Batch0448.certificate8974.rectangle,RoutedCases.Batch0448.certificate8975.rectangle,RoutedCases.Batch0448.certificate8976.rectangle,RoutedCases.Batch0448.certificate8977.rectangle,RoutedCases.Batch0448.certificate8978.rectangle,RoutedCases.Batch0448.certificate8979.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8960,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8962,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8968,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8970,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8971,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8972,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8974,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8975,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8976,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8977,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8978,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0448.sound8979,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(523/8000),(131/2000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source152
