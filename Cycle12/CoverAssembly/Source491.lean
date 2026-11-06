import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1004
import Cycle12.RoutedCases.Batch1005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source491

def strip0 : RatCoverRectangle := ⟨(13/200),(33/500),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1004.certificate20149.rectangle,RoutedCases.Batch1004.certificate20150.rectangle,RoutedCases.Batch1004.certificate20151.rectangle,RoutedCases.Batch1004.certificate20152.rectangle,RoutedCases.Batch1004.certificate20153.rectangle,RoutedCases.Batch1005.certificate20154.rectangle,RoutedCases.Batch1005.certificate20155.rectangle,RoutedCases.Batch1005.certificate20156.rectangle,RoutedCases.Batch1005.certificate20157.rectangle,DirectCases.Batch002.certificate20158.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20149,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20150,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20151,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20152,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20153,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20154,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20155,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20156,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1005.sound20157,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20158,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/200),(33/500),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source491
