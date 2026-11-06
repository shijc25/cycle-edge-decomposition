import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch0997
import Cycle12.RoutedCases.Batch0998

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source479

def strip0 : RatCoverRectangle := ⟨(53/1000),(27/500),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0997.certificate19987.rectangle,RoutedCases.Batch0997.certificate19988.rectangle,RoutedCases.Batch0997.certificate19989.rectangle,RoutedCases.Batch0997.certificate19990.rectangle,RoutedCases.Batch0997.certificate19991.rectangle,RoutedCases.Batch0997.certificate19992.rectangle,RoutedCases.Batch0997.certificate19993.rectangle,RoutedCases.Batch0997.certificate19994.rectangle,RoutedCases.Batch0997.certificate19995.rectangle,RoutedCases.Batch0997.certificate19996.rectangle,RoutedCases.Batch0997.certificate19997.rectangle,RoutedCases.Batch0997.certificate19998.rectangle,RoutedCases.Batch0997.certificate19999.rectangle,RoutedCases.Batch0997.certificate20000.rectangle,RoutedCases.Batch0997.certificate20001.rectangle,RoutedCases.Batch0998.certificate20002.rectangle,DirectCases.Batch002.certificate20003.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19999,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound20000,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound20001,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20002,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20003,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(53/1000),(27/500),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source479
