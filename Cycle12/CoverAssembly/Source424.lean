import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0921

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source424

def strip0 : RatCoverRectangle := ⟨(3/250),(13/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0921.certificate18427.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0921.sound18427,List.forall_mem_nil _⟩)

def rectangle : RatCoverRectangle := ⟨(3/250),(13/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source424
