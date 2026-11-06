import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1002
import Cycle12.RoutedCases.Batch1003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source487

def strip0 : RatCoverRectangle := ⟨(61/1000),(31/500),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1002.certificate20105.rectangle,RoutedCases.Batch1002.certificate20106.rectangle,RoutedCases.Batch1002.certificate20107.rectangle,RoutedCases.Batch1002.certificate20108.rectangle,RoutedCases.Batch1002.certificate20109.rectangle,RoutedCases.Batch1003.certificate20110.rectangle,RoutedCases.Batch1003.certificate20111.rectangle,RoutedCases.Batch1003.certificate20112.rectangle,RoutedCases.Batch1003.certificate20113.rectangle,RoutedCases.Batch1003.certificate20114.rectangle,RoutedCases.Batch1003.certificate20115.rectangle,DirectCases.Batch002.certificate20116.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20106,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20107,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20108,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20109,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20110,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20111,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20112,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20113,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20114,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20115,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20116,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(61/1000),(31/500),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source487
