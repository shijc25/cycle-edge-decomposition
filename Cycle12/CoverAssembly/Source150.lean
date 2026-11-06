import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0445
import Cycle12.RoutedCases.Batch0446

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source150

def strip0 : RatCoverRectangle := ⟨(521/8000),(1043/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0445.certificate8914.rectangle,RoutedCases.Batch0445.certificate8915.rectangle,RoutedCases.Batch0445.certificate8917.rectangle,RoutedCases.Batch0445.certificate8919.rectangle,RoutedCases.Batch0446.certificate8921.rectangle,RoutedCases.Batch0446.certificate8923.rectangle,RoutedCases.Batch0446.certificate8924.rectangle,RoutedCases.Batch0446.certificate8925.rectangle,RoutedCases.Batch0446.certificate8926.rectangle,RoutedCases.Batch0446.certificate8927.rectangle,RoutedCases.Batch0446.certificate8928.rectangle,RoutedCases.Batch0446.certificate8929.rectangle,RoutedCases.Batch0446.certificate8930.rectangle,RoutedCases.Batch0446.certificate8931.rectangle,RoutedCases.Batch0446.certificate8932.rectangle,RoutedCases.Batch0446.certificate8933.rectangle,RoutedCases.Batch0446.certificate8934.rectangle,RoutedCases.Batch0446.certificate8935.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8914,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8915,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8917,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8919,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8933,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8934,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8935,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1043/16000),(261/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0445.certificate8916.rectangle,RoutedCases.Batch0445.certificate8918.rectangle,RoutedCases.Batch0446.certificate8920.rectangle,RoutedCases.Batch0446.certificate8922.rectangle,RoutedCases.Batch0446.certificate8923.rectangle,RoutedCases.Batch0446.certificate8924.rectangle,RoutedCases.Batch0446.certificate8925.rectangle,RoutedCases.Batch0446.certificate8926.rectangle,RoutedCases.Batch0446.certificate8927.rectangle,RoutedCases.Batch0446.certificate8928.rectangle,RoutedCases.Batch0446.certificate8929.rectangle,RoutedCases.Batch0446.certificate8930.rectangle,RoutedCases.Batch0446.certificate8931.rectangle,RoutedCases.Batch0446.certificate8932.rectangle,RoutedCases.Batch0446.certificate8933.rectangle,RoutedCases.Batch0446.certificate8934.rectangle,RoutedCases.Batch0446.certificate8935.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8916,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0445.sound8918,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8920,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8933,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8934,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0446.sound8935,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(521/8000),(261/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source150
