import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source493

def strip0 : RatCoverRectangle := ⟨(67/1000),(17/250),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1005.certificate20168.rectangle,RoutedCases.Batch1005.certificate20169.rectangle,RoutedCases.Batch1005.certificate20170.rectangle,RoutedCases.Batch1005.certificate20171.rectangle,RoutedCases.Batch1005.certificate20172.rectangle,RoutedCases.Batch1005.certificate20173.rectangle,RoutedCases.Batch1005.certificate20174.rectangle,DirectCases.Batch002.certificate20175.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20168,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20169,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20170,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20171,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20172,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20173,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20174,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20175,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(67/1000),(17/250),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source493
