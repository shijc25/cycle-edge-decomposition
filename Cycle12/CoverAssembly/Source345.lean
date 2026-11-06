import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0836

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source345

def strip0 : RatCoverRectangle := ⟨(29/2000),(59/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16720.rectangle,RoutedCases.Batch0836.certificate16721.rectangle,RoutedCases.Batch0836.certificate16722.rectangle,RoutedCases.Batch0836.certificate16723.rectangle,RoutedCases.Batch0836.certificate16724.rectangle,RoutedCases.Batch0836.certificate16726.rectangle,RoutedCases.Batch0836.certificate16728.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16720,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16721,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16722,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16723,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16724,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16726,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16728,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(59/4000),(3/200),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0836.certificate16720.rectangle,RoutedCases.Batch0836.certificate16721.rectangle,RoutedCases.Batch0836.certificate16722.rectangle,RoutedCases.Batch0836.certificate16723.rectangle,RoutedCases.Batch0836.certificate16725.rectangle,RoutedCases.Batch0836.certificate16727.rectangle,RoutedCases.Batch0836.certificate16729.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16720,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16721,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16722,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16723,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16725,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16727,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0836.sound16729,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(29/2000),(3/200),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source345
