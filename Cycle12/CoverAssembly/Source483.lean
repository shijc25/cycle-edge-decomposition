import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source483

def strip0 : RatCoverRectangle := ⟨(57/1000),(29/500),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1000.certificate20051.rectangle,RoutedCases.Batch1000.certificate20052.rectangle,RoutedCases.Batch1000.certificate20053.rectangle,RoutedCases.Batch1000.certificate20054.rectangle,RoutedCases.Batch1000.certificate20055.rectangle,RoutedCases.Batch1000.certificate20056.rectangle,RoutedCases.Batch1000.certificate20057.rectangle,RoutedCases.Batch1000.certificate20058.rectangle,RoutedCases.Batch1000.certificate20059.rectangle,RoutedCases.Batch1000.certificate20060.rectangle,RoutedCases.Batch1000.certificate20061.rectangle,RoutedCases.Batch1000.certificate20062.rectangle,RoutedCases.Batch1000.certificate20063.rectangle,DirectCases.Batch002.certificate20064.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20060,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20061,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20062,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20063,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20064,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(57/1000),(29/500),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source483
