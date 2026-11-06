import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source492

def strip0 : RatCoverRectangle := ⟨(33/500),(67/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1005.certificate20159.rectangle,RoutedCases.Batch1005.certificate20160.rectangle,RoutedCases.Batch1005.certificate20161.rectangle,RoutedCases.Batch1005.certificate20162.rectangle,RoutedCases.Batch1005.certificate20163.rectangle,RoutedCases.Batch1005.certificate20164.rectangle,RoutedCases.Batch1005.certificate20165.rectangle,RoutedCases.Batch1005.certificate20166.rectangle,DirectCases.Batch002.certificate20167.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20159,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20160,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20161,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20162,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20163,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20164,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20165,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20166,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20167,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(33/500),(67/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source492
