import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch0999
import Cycle12.RoutedCases.Batch1000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source482

def strip0 : RatCoverRectangle := ⟨(7/125),(57/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0999.certificate20036.rectangle,RoutedCases.Batch0999.certificate20037.rectangle,RoutedCases.Batch0999.certificate20038.rectangle,RoutedCases.Batch0999.certificate20039.rectangle,RoutedCases.Batch0999.certificate20040.rectangle,RoutedCases.Batch0999.certificate20041.rectangle,RoutedCases.Batch0999.certificate20042.rectangle,RoutedCases.Batch0999.certificate20043.rectangle,RoutedCases.Batch0999.certificate20044.rectangle,RoutedCases.Batch1000.certificate20045.rectangle,RoutedCases.Batch1000.certificate20046.rectangle,RoutedCases.Batch1000.certificate20047.rectangle,RoutedCases.Batch1000.certificate20048.rectangle,RoutedCases.Batch1000.certificate20049.rectangle,DirectCases.Batch002.certificate20050.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20036,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20037,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20038,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20039,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20040,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20043,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20045,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20046,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20047,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1000.sound20049,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20050,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/125),(57/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source482
