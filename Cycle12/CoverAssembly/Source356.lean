import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0844
import Cycle12.RoutedCases.Batch0845

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source356

def strip0 : RatCoverRectangle := ⟨(9/400),(91/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0844.certificate16894.rectangle,RoutedCases.Batch0844.certificate16895.rectangle,RoutedCases.Batch0844.certificate16896.rectangle,RoutedCases.Batch0844.certificate16897.rectangle,RoutedCases.Batch0844.certificate16898.rectangle,RoutedCases.Batch0845.certificate16900.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16894,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16895,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16896,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16897,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16898,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16900,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(91/4000),(23/1000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0844.certificate16894.rectangle,RoutedCases.Batch0844.certificate16895.rectangle,RoutedCases.Batch0844.certificate16896.rectangle,RoutedCases.Batch0844.certificate16897.rectangle,RoutedCases.Batch0844.certificate16899.rectangle,RoutedCases.Batch0845.certificate16901.rectangle,RoutedCases.Batch0845.certificate16902.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16894,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16895,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16896,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16897,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0844.sound16899,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16901,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16902,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/400),(23/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source356
