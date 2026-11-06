import Cycle12.RationalCoverAssembly
import Cycle12.CoverAssembly.Source001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.SmallTail

def rectangle : RatCoverRectangle := ⟨0,(3/1000),2,none⟩
def pieces : List RatCoverRectangle := [CoverAssembly.Source001.rectangle]
theorem valid : rectangle.JoinX pieces := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle pieces valid (by
  exact List.forall_mem_cons.mpr ⟨CoverAssembly.Source001.sound,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.SmallTail
