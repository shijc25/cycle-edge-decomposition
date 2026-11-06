import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0423
import Cycle12.RoutedCases.Batch0424

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source132

def strip0 : RatCoverRectangle := ⟨(501/8000),(1003/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0423.certificate8471.rectangle,RoutedCases.Batch0423.certificate8472.rectangle,RoutedCases.Batch0423.certificate8474.rectangle,RoutedCases.Batch0423.certificate8476.rectangle,RoutedCases.Batch0423.certificate8478.rectangle,RoutedCases.Batch0424.certificate8480.rectangle,RoutedCases.Batch0424.certificate8481.rectangle,RoutedCases.Batch0424.certificate8482.rectangle,RoutedCases.Batch0424.certificate8483.rectangle,RoutedCases.Batch0424.certificate8484.rectangle,RoutedCases.Batch0424.certificate8485.rectangle,RoutedCases.Batch0424.certificate8486.rectangle,RoutedCases.Batch0424.certificate8487.rectangle,RoutedCases.Batch0424.certificate8488.rectangle,RoutedCases.Batch0424.certificate8489.rectangle,RoutedCases.Batch0424.certificate8490.rectangle,RoutedCases.Batch0424.certificate8491.rectangle,RoutedCases.Batch0424.certificate8492.rectangle,RoutedCases.Batch0424.certificate8493.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8471,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8472,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8474,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8484,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8485,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8486,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8488,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8489,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8490,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8491,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8492,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8493,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1003/16000),(251/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0423.certificate8473.rectangle,RoutedCases.Batch0423.certificate8475.rectangle,RoutedCases.Batch0423.certificate8477.rectangle,RoutedCases.Batch0423.certificate8479.rectangle,RoutedCases.Batch0424.certificate8480.rectangle,RoutedCases.Batch0424.certificate8481.rectangle,RoutedCases.Batch0424.certificate8482.rectangle,RoutedCases.Batch0424.certificate8483.rectangle,RoutedCases.Batch0424.certificate8484.rectangle,RoutedCases.Batch0424.certificate8485.rectangle,RoutedCases.Batch0424.certificate8486.rectangle,RoutedCases.Batch0424.certificate8487.rectangle,RoutedCases.Batch0424.certificate8488.rectangle,RoutedCases.Batch0424.certificate8489.rectangle,RoutedCases.Batch0424.certificate8490.rectangle,RoutedCases.Batch0424.certificate8491.rectangle,RoutedCases.Batch0424.certificate8492.rectangle,RoutedCases.Batch0424.certificate8493.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8473,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8475,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8484,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8485,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8486,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8488,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8489,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8490,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8491,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8492,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0424.sound8493,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(501/8000),(251/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source132
