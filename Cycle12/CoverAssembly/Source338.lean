import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0830
import Cycle12.RoutedCases.Batch0831

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source338

def strip0 : RatCoverRectangle := ⟨(1/100),(41/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0830.certificate16613.rectangle,RoutedCases.Batch0830.certificate16614.rectangle,RoutedCases.Batch0830.certificate16615.rectangle,RoutedCases.Batch0830.certificate16616.rectangle,RoutedCases.Batch0830.certificate16618.rectangle,RoutedCases.Batch0831.certificate16620.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16620,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(41/4000),(21/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0830.certificate16613.rectangle,RoutedCases.Batch0830.certificate16614.rectangle,RoutedCases.Batch0830.certificate16615.rectangle,RoutedCases.Batch0830.certificate16617.rectangle,RoutedCases.Batch0830.certificate16619.rectangle,RoutedCases.Batch0831.certificate16621.rectangle,RoutedCases.Batch0831.certificate16622.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16619,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16621,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16622,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/100),(21/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source338
