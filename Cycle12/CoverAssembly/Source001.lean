import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source001

def strip0 : RatCoverRectangle := ⟨0,(3/1000),2,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0000.certificate1.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound1,List.forall_mem_nil _⟩)

def rectangle : RatCoverRectangle := ⟨0,(3/1000),2,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source001
