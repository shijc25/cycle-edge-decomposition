import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch0995
import Cycle12.RoutedCases.Batch0996

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source477

def strip0 : RatCoverRectangle := ⟨(51/1000),(13/250),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0995.certificate19950.rectangle,RoutedCases.Batch0995.certificate19951.rectangle,RoutedCases.Batch0995.certificate19952.rectangle,RoutedCases.Batch0995.certificate19953.rectangle,RoutedCases.Batch0995.certificate19954.rectangle,RoutedCases.Batch0995.certificate19955.rectangle,RoutedCases.Batch0995.certificate19956.rectangle,RoutedCases.Batch0995.certificate19957.rectangle,RoutedCases.Batch0995.certificate19958.rectangle,RoutedCases.Batch0995.certificate19959.rectangle,RoutedCases.Batch0996.certificate19960.rectangle,RoutedCases.Batch0996.certificate19961.rectangle,RoutedCases.Batch0996.certificate19962.rectangle,RoutedCases.Batch0996.certificate19963.rectangle,RoutedCases.Batch0996.certificate19964.rectangle,RoutedCases.Batch0996.certificate19965.rectangle,RoutedCases.Batch0996.certificate19966.rectangle,RoutedCases.Batch0996.certificate19967.rectangle,DirectCases.Batch002.certificate19968.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19951,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19952,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19953,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19954,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19955,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19956,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19957,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19958,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0995.sound19959,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19960,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19961,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19962,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19963,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19967,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound19968,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(51/1000),(13/250),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source477
