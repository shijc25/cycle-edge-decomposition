import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0436
import Cycle12.RoutedCases.Batch0437

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source142

def strip0 : RatCoverRectangle := ⟨(513/8000),(1027/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0436.certificate8739.rectangle,RoutedCases.Batch0437.certificate8740.rectangle,RoutedCases.Batch0437.certificate8742.rectangle,RoutedCases.Batch0437.certificate8744.rectangle,RoutedCases.Batch0437.certificate8746.rectangle,RoutedCases.Batch0437.certificate8747.rectangle,RoutedCases.Batch0437.certificate8748.rectangle,RoutedCases.Batch0437.certificate8749.rectangle,RoutedCases.Batch0437.certificate8750.rectangle,RoutedCases.Batch0437.certificate8751.rectangle,RoutedCases.Batch0437.certificate8752.rectangle,RoutedCases.Batch0437.certificate8753.rectangle,RoutedCases.Batch0437.certificate8754.rectangle,RoutedCases.Batch0437.certificate8755.rectangle,RoutedCases.Batch0437.certificate8756.rectangle,RoutedCases.Batch0437.certificate8757.rectangle,RoutedCases.Batch0437.certificate8758.rectangle,RoutedCases.Batch0437.certificate8759.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8739,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8740,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8742,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8744,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8747,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8748,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8749,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8750,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8751,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8752,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8753,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8754,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8755,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8756,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8757,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8758,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8759,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1027/16000),(257/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0437.certificate8741.rectangle,RoutedCases.Batch0437.certificate8743.rectangle,RoutedCases.Batch0437.certificate8745.rectangle,RoutedCases.Batch0437.certificate8746.rectangle,RoutedCases.Batch0437.certificate8747.rectangle,RoutedCases.Batch0437.certificate8748.rectangle,RoutedCases.Batch0437.certificate8749.rectangle,RoutedCases.Batch0437.certificate8750.rectangle,RoutedCases.Batch0437.certificate8751.rectangle,RoutedCases.Batch0437.certificate8752.rectangle,RoutedCases.Batch0437.certificate8753.rectangle,RoutedCases.Batch0437.certificate8754.rectangle,RoutedCases.Batch0437.certificate8755.rectangle,RoutedCases.Batch0437.certificate8756.rectangle,RoutedCases.Batch0437.certificate8757.rectangle,RoutedCases.Batch0437.certificate8758.rectangle,RoutedCases.Batch0437.certificate8759.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8741,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8743,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8745,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8746,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8747,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8748,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8749,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8750,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8751,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8752,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8753,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8754,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8755,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8756,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8757,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8758,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0437.sound8759,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(513/8000),(257/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source142
