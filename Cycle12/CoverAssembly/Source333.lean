import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0827
import Cycle12.RoutedCases.Batch0828

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source333

def strip0 : RatCoverRectangle := ⟨(7/1000),(29/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0827.certificate16559.rectangle,RoutedCases.Batch0828.certificate16560.rectangle,RoutedCases.Batch0828.certificate16561.rectangle,RoutedCases.Batch0828.certificate16562.rectangle,RoutedCases.Batch0828.certificate16564.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16559,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16560,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16561,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16562,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16564,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(29/4000),(3/400),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0827.certificate16559.rectangle,RoutedCases.Batch0828.certificate16560.rectangle,RoutedCases.Batch0828.certificate16561.rectangle,RoutedCases.Batch0828.certificate16563.rectangle,RoutedCases.Batch0828.certificate16564.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16559,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16560,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16561,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16563,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16564,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/1000),(3/400),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source333
