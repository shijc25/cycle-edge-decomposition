import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0395
import Cycle12.RoutedCases.Batch0396

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source114

def strip0 : RatCoverRectangle := ⟨(471/8000),(943/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0395.certificate7907.rectangle,RoutedCases.Batch0395.certificate7908.rectangle,RoutedCases.Batch0395.certificate7910.rectangle,RoutedCases.Batch0395.certificate7912.rectangle,RoutedCases.Batch0395.certificate7914.rectangle,RoutedCases.Batch0395.certificate7916.rectangle,RoutedCases.Batch0395.certificate7918.rectangle,RoutedCases.Batch0395.certificate7919.rectangle,RoutedCases.Batch0396.certificate7920.rectangle,RoutedCases.Batch0396.certificate7921.rectangle,RoutedCases.Batch0396.certificate7922.rectangle,RoutedCases.Batch0396.certificate7923.rectangle,RoutedCases.Batch0396.certificate7924.rectangle,RoutedCases.Batch0396.certificate7925.rectangle,RoutedCases.Batch0396.certificate7926.rectangle,RoutedCases.Batch0396.certificate7927.rectangle,RoutedCases.Batch0396.certificate7928.rectangle,RoutedCases.Batch0396.certificate7929.rectangle,RoutedCases.Batch0396.certificate7930.rectangle,RoutedCases.Batch0396.certificate7931.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7907,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7908,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7910,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7912,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7914,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7916,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7918,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7919,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7920,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7931,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(943/16000),(59/1000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0395.certificate7909.rectangle,RoutedCases.Batch0395.certificate7911.rectangle,RoutedCases.Batch0395.certificate7913.rectangle,RoutedCases.Batch0395.certificate7915.rectangle,RoutedCases.Batch0395.certificate7917.rectangle,RoutedCases.Batch0395.certificate7918.rectangle,RoutedCases.Batch0395.certificate7919.rectangle,RoutedCases.Batch0396.certificate7920.rectangle,RoutedCases.Batch0396.certificate7921.rectangle,RoutedCases.Batch0396.certificate7922.rectangle,RoutedCases.Batch0396.certificate7923.rectangle,RoutedCases.Batch0396.certificate7924.rectangle,RoutedCases.Batch0396.certificate7925.rectangle,RoutedCases.Batch0396.certificate7926.rectangle,RoutedCases.Batch0396.certificate7927.rectangle,RoutedCases.Batch0396.certificate7928.rectangle,RoutedCases.Batch0396.certificate7929.rectangle,RoutedCases.Batch0396.certificate7930.rectangle,RoutedCases.Batch0396.certificate7931.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7909,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7911,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7913,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7915,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7917,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7918,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0395.sound7919,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7920,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0396.sound7931,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(471/8000),(59/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source114
