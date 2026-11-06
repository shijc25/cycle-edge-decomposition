import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0451
import Cycle12.RoutedCases.Batch0452

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source155

def strip0 : RatCoverRectangle := ⟨(263/4000),(1053/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0451.certificate9023.rectangle,RoutedCases.Batch0451.certificate9025.rectangle,RoutedCases.Batch0451.certificate9027.rectangle,RoutedCases.Batch0451.certificate9029.rectangle,RoutedCases.Batch0451.certificate9030.rectangle,RoutedCases.Batch0451.certificate9031.rectangle,RoutedCases.Batch0451.certificate9032.rectangle,RoutedCases.Batch0451.certificate9033.rectangle,RoutedCases.Batch0451.certificate9034.rectangle,RoutedCases.Batch0451.certificate9035.rectangle,RoutedCases.Batch0451.certificate9036.rectangle,RoutedCases.Batch0451.certificate9037.rectangle,RoutedCases.Batch0451.certificate9038.rectangle,RoutedCases.Batch0451.certificate9039.rectangle,RoutedCases.Batch0452.certificate9040.rectangle,RoutedCases.Batch0452.certificate9041.rectangle,RoutedCases.Batch0452.certificate9042.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9023,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9025,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9027,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9031,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9032,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9034,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9035,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9036,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9037,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9038,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9039,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9040,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9042,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1053/16000),(527/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0451.certificate9024.rectangle,RoutedCases.Batch0451.certificate9026.rectangle,RoutedCases.Batch0451.certificate9028.rectangle,RoutedCases.Batch0451.certificate9029.rectangle,RoutedCases.Batch0451.certificate9030.rectangle,RoutedCases.Batch0451.certificate9031.rectangle,RoutedCases.Batch0451.certificate9032.rectangle,RoutedCases.Batch0451.certificate9033.rectangle,RoutedCases.Batch0451.certificate9034.rectangle,RoutedCases.Batch0451.certificate9035.rectangle,RoutedCases.Batch0451.certificate9036.rectangle,RoutedCases.Batch0451.certificate9037.rectangle,RoutedCases.Batch0451.certificate9038.rectangle,RoutedCases.Batch0451.certificate9039.rectangle,RoutedCases.Batch0452.certificate9040.rectangle,RoutedCases.Batch0452.certificate9041.rectangle,RoutedCases.Batch0452.certificate9042.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9024,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9026,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9028,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9029,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9030,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9031,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9032,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9033,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9034,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9035,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9036,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9037,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9038,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9039,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9040,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9042,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(263/4000),(527/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source155
