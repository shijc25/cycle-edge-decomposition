import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1000
import Cycle12.RoutedCases.Batch1001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source484

def strip0 : RatCoverRectangle := ⟨(29/500),(59/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1000.certificate20065.rectangle,RoutedCases.Batch1000.certificate20066.rectangle,RoutedCases.Batch1001.certificate20067.rectangle,RoutedCases.Batch1001.certificate20068.rectangle,RoutedCases.Batch1001.certificate20069.rectangle,RoutedCases.Batch1001.certificate20070.rectangle,RoutedCases.Batch1001.certificate20071.rectangle,RoutedCases.Batch1001.certificate20072.rectangle,RoutedCases.Batch1001.certificate20073.rectangle,RoutedCases.Batch1001.certificate20074.rectangle,RoutedCases.Batch1001.certificate20075.rectangle,RoutedCases.Batch1001.certificate20076.rectangle,RoutedCases.Batch1001.certificate20077.rectangle,DirectCases.Batch002.certificate20078.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20065,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20066,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20067,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20072,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20073,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20074,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1001.sound20077,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20078,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(29/500),(59/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source484
