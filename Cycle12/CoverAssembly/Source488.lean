import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source488

def strip0 : RatCoverRectangle := ⟨(31/500),(63/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1003.certificate20117.rectangle,RoutedCases.Batch1003.certificate20118.rectangle,RoutedCases.Batch1003.certificate20119.rectangle,RoutedCases.Batch1003.certificate20120.rectangle,RoutedCases.Batch1003.certificate20121.rectangle,RoutedCases.Batch1003.certificate20122.rectangle,RoutedCases.Batch1003.certificate20123.rectangle,RoutedCases.Batch1003.certificate20124.rectangle,RoutedCases.Batch1003.certificate20125.rectangle,RoutedCases.Batch1003.certificate20126.rectangle,DirectCases.Batch002.certificate20127.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20117,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20120,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20122,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20124,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20125,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20126,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20127,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(31/500),(63/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source488
