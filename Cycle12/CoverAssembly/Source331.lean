import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0826

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source331

def strip0 : RatCoverRectangle := ⟨(11/2000),(23/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0826.certificate16531.rectangle,RoutedCases.Batch0826.certificate16532.rectangle,RoutedCases.Batch0826.certificate16533.rectangle,RoutedCases.Batch0826.certificate16534.rectangle,RoutedCases.Batch0826.certificate16536.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16531,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16532,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16533,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16534,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16536,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(23/4000),(3/500),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0826.certificate16531.rectangle,RoutedCases.Batch0826.certificate16532.rectangle,RoutedCases.Batch0826.certificate16533.rectangle,RoutedCases.Batch0826.certificate16535.rectangle,RoutedCases.Batch0826.certificate16537.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16531,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16532,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16533,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16535,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16537,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/2000),(3/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source331
