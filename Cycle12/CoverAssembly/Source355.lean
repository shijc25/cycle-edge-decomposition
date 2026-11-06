import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0844

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source355

def strip0 : RatCoverRectangle := ⟨(11/500),(89/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0844.certificate16885.rectangle,RoutedCases.Batch0844.certificate16886.rectangle,RoutedCases.Batch0844.certificate16887.rectangle,RoutedCases.Batch0844.certificate16888.rectangle,RoutedCases.Batch0844.certificate16889.rectangle,RoutedCases.Batch0844.certificate16891.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16889,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16891,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(89/4000),(9/400),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0844.certificate16885.rectangle,RoutedCases.Batch0844.certificate16886.rectangle,RoutedCases.Batch0844.certificate16887.rectangle,RoutedCases.Batch0844.certificate16888.rectangle,RoutedCases.Batch0844.certificate16890.rectangle,RoutedCases.Batch0844.certificate16892.rectangle,RoutedCases.Batch0844.certificate16893.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16892,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16893,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/500),(9/400),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source355
