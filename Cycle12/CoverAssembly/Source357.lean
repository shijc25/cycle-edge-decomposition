import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0845

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source357

def strip0 : RatCoverRectangle := ⟨(23/1000),(93/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0845.certificate16903.rectangle,RoutedCases.Batch0845.certificate16904.rectangle,RoutedCases.Batch0845.certificate16905.rectangle,RoutedCases.Batch0845.certificate16906.rectangle,RoutedCases.Batch0845.certificate16907.rectangle,RoutedCases.Batch0845.certificate16909.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16903,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16904,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16905,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16906,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16907,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16909,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(93/4000),(47/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0845.certificate16903.rectangle,RoutedCases.Batch0845.certificate16904.rectangle,RoutedCases.Batch0845.certificate16905.rectangle,RoutedCases.Batch0845.certificate16906.rectangle,RoutedCases.Batch0845.certificate16908.rectangle,RoutedCases.Batch0845.certificate16910.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16903,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16904,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16905,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16906,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16908,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16910,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(23/1000),(47/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source357
