import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch0996
import Cycle12.RoutedCases.Batch0997

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source478

def strip0 : RatCoverRectangle := ⟨(13/250),(53/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0996.certificate19969.rectangle,RoutedCases.Batch0996.certificate19970.rectangle,RoutedCases.Batch0996.certificate19971.rectangle,RoutedCases.Batch0996.certificate19972.rectangle,RoutedCases.Batch0996.certificate19973.rectangle,RoutedCases.Batch0996.certificate19974.rectangle,RoutedCases.Batch0996.certificate19975.rectangle,RoutedCases.Batch0996.certificate19976.rectangle,RoutedCases.Batch0996.certificate19977.rectangle,RoutedCases.Batch0996.certificate19978.rectangle,RoutedCases.Batch0996.certificate19979.rectangle,RoutedCases.Batch0996.certificate19980.rectangle,RoutedCases.Batch0997.certificate19981.rectangle,RoutedCases.Batch0997.certificate19982.rectangle,RoutedCases.Batch0997.certificate19983.rectangle,RoutedCases.Batch0997.certificate19984.rectangle,RoutedCases.Batch0997.certificate19985.rectangle,DirectCases.Batch002.certificate19986.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19970,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19971,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19972,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19974,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19975,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19976,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19977,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19978,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19979,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0996.sound19980,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19981,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19982,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19983,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19984,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0997.sound19985,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound19986,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/250),(53/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source478
