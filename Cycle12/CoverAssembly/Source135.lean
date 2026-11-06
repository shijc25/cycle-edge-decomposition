import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0428
import Cycle12.RoutedCases.Batch0429

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source135

def strip0 : RatCoverRectangle := ⟨(101/1600),(1011/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0428.certificate8562.rectangle,RoutedCases.Batch0428.certificate8563.rectangle,RoutedCases.Batch0428.certificate8565.rectangle,RoutedCases.Batch0428.certificate8567.rectangle,RoutedCases.Batch0428.certificate8569.rectangle,RoutedCases.Batch0428.certificate8571.rectangle,RoutedCases.Batch0428.certificate8572.rectangle,RoutedCases.Batch0428.certificate8573.rectangle,RoutedCases.Batch0428.certificate8574.rectangle,RoutedCases.Batch0428.certificate8575.rectangle,RoutedCases.Batch0428.certificate8576.rectangle,RoutedCases.Batch0428.certificate8577.rectangle,RoutedCases.Batch0428.certificate8578.rectangle,RoutedCases.Batch0428.certificate8579.rectangle,RoutedCases.Batch0429.certificate8580.rectangle,RoutedCases.Batch0429.certificate8581.rectangle,RoutedCases.Batch0429.certificate8582.rectangle,RoutedCases.Batch0429.certificate8583.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8562,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8563,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8565,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8567,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8569,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8571,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8581,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8582,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8583,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1011/16000),(253/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0428.certificate8564.rectangle,RoutedCases.Batch0428.certificate8566.rectangle,RoutedCases.Batch0428.certificate8568.rectangle,RoutedCases.Batch0428.certificate8570.rectangle,RoutedCases.Batch0428.certificate8571.rectangle,RoutedCases.Batch0428.certificate8572.rectangle,RoutedCases.Batch0428.certificate8573.rectangle,RoutedCases.Batch0428.certificate8574.rectangle,RoutedCases.Batch0428.certificate8575.rectangle,RoutedCases.Batch0428.certificate8576.rectangle,RoutedCases.Batch0428.certificate8577.rectangle,RoutedCases.Batch0428.certificate8578.rectangle,RoutedCases.Batch0428.certificate8579.rectangle,RoutedCases.Batch0429.certificate8580.rectangle,RoutedCases.Batch0429.certificate8581.rectangle,RoutedCases.Batch0429.certificate8582.rectangle,RoutedCases.Batch0429.certificate8583.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8564,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8566,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8568,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8570,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8571,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8581,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8582,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0429.sound8583,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(101/1600),(253/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source135
