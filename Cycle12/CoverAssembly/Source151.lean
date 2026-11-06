import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0446
import Cycle12.RoutedCases.Batch0447

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source151

def strip0 : RatCoverRectangle := ⟨(261/4000),(209/3200),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0446.certificate8936.rectangle,RoutedCases.Batch0446.certificate8937.rectangle,RoutedCases.Batch0446.certificate8939.rectangle,RoutedCases.Batch0447.certificate8941.rectangle,RoutedCases.Batch0447.certificate8943.rectangle,RoutedCases.Batch0447.certificate8945.rectangle,RoutedCases.Batch0447.certificate8946.rectangle,RoutedCases.Batch0447.certificate8947.rectangle,RoutedCases.Batch0447.certificate8948.rectangle,RoutedCases.Batch0447.certificate8949.rectangle,RoutedCases.Batch0447.certificate8950.rectangle,RoutedCases.Batch0447.certificate8951.rectangle,RoutedCases.Batch0447.certificate8952.rectangle,RoutedCases.Batch0447.certificate8953.rectangle,RoutedCases.Batch0447.certificate8954.rectangle,RoutedCases.Batch0447.certificate8955.rectangle,RoutedCases.Batch0447.certificate8956.rectangle,RoutedCases.Batch0447.certificate8957.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8936,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8937,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8939,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8951,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8952,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8953,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8954,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8955,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8956,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8957,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(209/3200),(523/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0446.certificate8938.rectangle,RoutedCases.Batch0447.certificate8940.rectangle,RoutedCases.Batch0447.certificate8942.rectangle,RoutedCases.Batch0447.certificate8944.rectangle,RoutedCases.Batch0447.certificate8945.rectangle,RoutedCases.Batch0447.certificate8946.rectangle,RoutedCases.Batch0447.certificate8947.rectangle,RoutedCases.Batch0447.certificate8948.rectangle,RoutedCases.Batch0447.certificate8949.rectangle,RoutedCases.Batch0447.certificate8950.rectangle,RoutedCases.Batch0447.certificate8951.rectangle,RoutedCases.Batch0447.certificate8952.rectangle,RoutedCases.Batch0447.certificate8953.rectangle,RoutedCases.Batch0447.certificate8954.rectangle,RoutedCases.Batch0447.certificate8955.rectangle,RoutedCases.Batch0447.certificate8956.rectangle,RoutedCases.Batch0447.certificate8957.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8938,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8940,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8951,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8952,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8953,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8954,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8955,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8956,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0447.sound8957,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(261/4000),(523/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source151
