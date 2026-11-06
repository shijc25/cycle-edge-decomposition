import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0921
import Cycle12.RoutedCases.Batch0922

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source436

def strip0 : RatCoverRectangle := ⟨(3/125),(49/2000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0921.certificate18439.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0921.sound18439,List.forall_mem_nil _⟩)

def strip1 : RatCoverRectangle := ⟨(49/2000),(1/40),100,none⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0922.certificate18440.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0922.sound18440,List.forall_mem_nil _⟩)

def rectangle : RatCoverRectangle := ⟨(3/125),(1/40),100,none⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source436
