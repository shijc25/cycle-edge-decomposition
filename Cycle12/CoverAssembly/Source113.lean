import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0394
import Cycle12.RoutedCases.Batch0395

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source113

def strip0 : RatCoverRectangle := ⟨(47/800),(941/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0394.certificate7885.rectangle,RoutedCases.Batch0394.certificate7887.rectangle,RoutedCases.Batch0394.certificate7889.rectangle,RoutedCases.Batch0394.certificate7891.rectangle,RoutedCases.Batch0394.certificate7893.rectangle,RoutedCases.Batch0394.certificate7894.rectangle,RoutedCases.Batch0394.certificate7895.rectangle,RoutedCases.Batch0394.certificate7896.rectangle,RoutedCases.Batch0394.certificate7897.rectangle,RoutedCases.Batch0394.certificate7898.rectangle,RoutedCases.Batch0394.certificate7899.rectangle,RoutedCases.Batch0395.certificate7900.rectangle,RoutedCases.Batch0395.certificate7901.rectangle,RoutedCases.Batch0395.certificate7902.rectangle,RoutedCases.Batch0395.certificate7903.rectangle,RoutedCases.Batch0395.certificate7904.rectangle,RoutedCases.Batch0395.certificate7905.rectangle,RoutedCases.Batch0395.certificate7906.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7889,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7891,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7893,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7894,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7895,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7896,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7897,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7898,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7899,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7900,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7901,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7902,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7903,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7904,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7905,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7906,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(941/16000),(471/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0394.certificate7886.rectangle,RoutedCases.Batch0394.certificate7888.rectangle,RoutedCases.Batch0394.certificate7890.rectangle,RoutedCases.Batch0394.certificate7892.rectangle,RoutedCases.Batch0394.certificate7893.rectangle,RoutedCases.Batch0394.certificate7894.rectangle,RoutedCases.Batch0394.certificate7895.rectangle,RoutedCases.Batch0394.certificate7896.rectangle,RoutedCases.Batch0394.certificate7897.rectangle,RoutedCases.Batch0394.certificate7898.rectangle,RoutedCases.Batch0394.certificate7899.rectangle,RoutedCases.Batch0395.certificate7900.rectangle,RoutedCases.Batch0395.certificate7901.rectangle,RoutedCases.Batch0395.certificate7902.rectangle,RoutedCases.Batch0395.certificate7903.rectangle,RoutedCases.Batch0395.certificate7904.rectangle,RoutedCases.Batch0395.certificate7905.rectangle,RoutedCases.Batch0395.certificate7906.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7892,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7893,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7894,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7895,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7896,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7897,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7898,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0394.sound7899,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7900,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7901,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7902,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7903,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7904,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7905,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7906,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(47/800),(471/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source113
