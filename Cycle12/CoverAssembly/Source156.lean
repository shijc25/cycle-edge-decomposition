import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0452
import Cycle12.RoutedCases.Batch0453

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source156

def strip0 : RatCoverRectangle := ⟨(527/8000),(211/3200),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0452.certificate9043.rectangle,RoutedCases.Batch0452.certificate9045.rectangle,RoutedCases.Batch0452.certificate9047.rectangle,RoutedCases.Batch0452.certificate9049.rectangle,RoutedCases.Batch0452.certificate9050.rectangle,RoutedCases.Batch0452.certificate9051.rectangle,RoutedCases.Batch0452.certificate9052.rectangle,RoutedCases.Batch0452.certificate9053.rectangle,RoutedCases.Batch0452.certificate9054.rectangle,RoutedCases.Batch0452.certificate9055.rectangle,RoutedCases.Batch0452.certificate9056.rectangle,RoutedCases.Batch0452.certificate9057.rectangle,RoutedCases.Batch0452.certificate9058.rectangle,RoutedCases.Batch0452.certificate9059.rectangle,RoutedCases.Batch0453.certificate9060.rectangle,RoutedCases.Batch0453.certificate9061.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9043,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9045,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9047,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0453.sound9060,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0453.sound9061,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(211/3200),(33/500),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0452.certificate9044.rectangle,RoutedCases.Batch0452.certificate9046.rectangle,RoutedCases.Batch0452.certificate9048.rectangle,RoutedCases.Batch0452.certificate9049.rectangle,RoutedCases.Batch0452.certificate9050.rectangle,RoutedCases.Batch0452.certificate9051.rectangle,RoutedCases.Batch0452.certificate9052.rectangle,RoutedCases.Batch0452.certificate9053.rectangle,RoutedCases.Batch0452.certificate9054.rectangle,RoutedCases.Batch0452.certificate9055.rectangle,RoutedCases.Batch0452.certificate9056.rectangle,RoutedCases.Batch0452.certificate9057.rectangle,RoutedCases.Batch0452.certificate9058.rectangle,RoutedCases.Batch0452.certificate9059.rectangle,RoutedCases.Batch0453.certificate9060.rectangle,RoutedCases.Batch0453.certificate9061.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9046,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0452.sound9059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0453.sound9060,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0453.sound9061,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(527/8000),(33/500),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source156
