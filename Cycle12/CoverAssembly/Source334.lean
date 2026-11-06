import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0828

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source334

def strip0 : RatCoverRectangle := ⟨(3/400),(31/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0828.certificate16565.rectangle,RoutedCases.Batch0828.certificate16566.rectangle,RoutedCases.Batch0828.certificate16567.rectangle,RoutedCases.Batch0828.certificate16568.rectangle,RoutedCases.Batch0828.certificate16570.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16565,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16566,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16567,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16568,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16570,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(31/4000),(1/125),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0828.certificate16565.rectangle,RoutedCases.Batch0828.certificate16566.rectangle,RoutedCases.Batch0828.certificate16567.rectangle,RoutedCases.Batch0828.certificate16569.rectangle,RoutedCases.Batch0828.certificate16571.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16565,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16566,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16567,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16569,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16571,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/400),(1/125),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source334
