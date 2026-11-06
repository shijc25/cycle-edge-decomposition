import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1001
import Cycle12.RoutedCases.Batch1002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source485

def strip0 : RatCoverRectangle := ⟨(59/1000),(3/50),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1001.certificate20079.rectangle,RoutedCases.Batch1001.certificate20080.rectangle,RoutedCases.Batch1001.certificate20081.rectangle,RoutedCases.Batch1001.certificate20082.rectangle,RoutedCases.Batch1001.certificate20083.rectangle,RoutedCases.Batch1001.certificate20084.rectangle,RoutedCases.Batch1001.certificate20085.rectangle,RoutedCases.Batch1001.certificate20086.rectangle,RoutedCases.Batch1001.certificate20087.rectangle,RoutedCases.Batch1002.certificate20088.rectangle,RoutedCases.Batch1002.certificate20089.rectangle,RoutedCases.Batch1002.certificate20090.rectangle,DirectCases.Batch002.certificate20091.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20079,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20080,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20081,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20082,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20083,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20084,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20085,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20086,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20087,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20088,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20089,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20090,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20091,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(59/1000),(3/50),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source485
