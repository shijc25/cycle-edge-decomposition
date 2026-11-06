import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch0998

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source480

def strip0 : RatCoverRectangle := ⟨(27/500),(11/200),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0998.certificate20004.rectangle,RoutedCases.Batch0998.certificate20005.rectangle,RoutedCases.Batch0998.certificate20006.rectangle,RoutedCases.Batch0998.certificate20007.rectangle,RoutedCases.Batch0998.certificate20008.rectangle,RoutedCases.Batch0998.certificate20009.rectangle,RoutedCases.Batch0998.certificate20010.rectangle,RoutedCases.Batch0998.certificate20011.rectangle,RoutedCases.Batch0998.certificate20012.rectangle,RoutedCases.Batch0998.certificate20013.rectangle,RoutedCases.Batch0998.certificate20014.rectangle,RoutedCases.Batch0998.certificate20015.rectangle,RoutedCases.Batch0998.certificate20016.rectangle,RoutedCases.Batch0998.certificate20017.rectangle,RoutedCases.Batch0998.certificate20018.rectangle,DirectCases.Batch002.certificate20019.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20008,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20009,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20011,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20012,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20013,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20018,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20019,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(27/500),(11/200),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source480
