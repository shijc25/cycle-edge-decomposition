import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0833

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source341

def strip0 : RatCoverRectangle := ⟨(3/250),(49/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0833.certificate16663.rectangle,RoutedCases.Batch0833.certificate16664.rectangle,RoutedCases.Batch0833.certificate16665.rectangle,RoutedCases.Batch0833.certificate16666.rectangle,RoutedCases.Batch0833.certificate16667.rectangle,RoutedCases.Batch0833.certificate16669.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16663,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16664,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16665,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16666,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16667,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16669,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(49/4000),(1/80),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0833.certificate16663.rectangle,RoutedCases.Batch0833.certificate16664.rectangle,RoutedCases.Batch0833.certificate16665.rectangle,RoutedCases.Batch0833.certificate16666.rectangle,RoutedCases.Batch0833.certificate16668.rectangle,RoutedCases.Batch0833.certificate16670.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16663,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16664,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16665,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16666,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16668,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16670,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/250),(1/80),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source341
