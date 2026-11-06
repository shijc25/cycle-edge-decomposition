import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch0998
import Cycle12.RoutedCases.Batch0999

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source481

def strip0 : RatCoverRectangle := ⟨(11/200),(7/125),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0998.certificate20020.rectangle,RoutedCases.Batch0998.certificate20021.rectangle,RoutedCases.Batch0998.certificate20022.rectangle,RoutedCases.Batch0998.certificate20023.rectangle,RoutedCases.Batch0999.certificate20024.rectangle,RoutedCases.Batch0999.certificate20025.rectangle,RoutedCases.Batch0999.certificate20026.rectangle,RoutedCases.Batch0999.certificate20027.rectangle,RoutedCases.Batch0999.certificate20028.rectangle,RoutedCases.Batch0999.certificate20029.rectangle,RoutedCases.Batch0999.certificate20030.rectangle,RoutedCases.Batch0999.certificate20031.rectangle,RoutedCases.Batch0999.certificate20032.rectangle,RoutedCases.Batch0999.certificate20033.rectangle,RoutedCases.Batch0999.certificate20034.rectangle,DirectCases.Batch002.certificate20035.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20020,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20021,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20022,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0998.sound20023,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20024,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20025,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20026,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20031,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20032,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0999.sound20034,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20035,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/200),(7/125),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source481
