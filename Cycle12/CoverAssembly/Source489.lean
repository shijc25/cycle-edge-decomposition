import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1003
import Cycle12.RoutedCases.Batch1004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source489

def strip0 : RatCoverRectangle := ⟨(63/1000),(8/125),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1003.certificate20128.rectangle,RoutedCases.Batch1003.certificate20129.rectangle,RoutedCases.Batch1003.certificate20130.rectangle,RoutedCases.Batch1003.certificate20131.rectangle,RoutedCases.Batch1004.certificate20132.rectangle,RoutedCases.Batch1004.certificate20133.rectangle,RoutedCases.Batch1004.certificate20134.rectangle,RoutedCases.Batch1004.certificate20135.rectangle,RoutedCases.Batch1004.certificate20136.rectangle,RoutedCases.Batch1004.certificate20137.rectangle,DirectCases.Batch002.certificate20138.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20129,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1003.sound20131,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20133,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20134,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20137,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20138,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(63/1000),(8/125),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source489
