import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0450
import Cycle12.RoutedCases.Batch0451

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source154

def strip0 : RatCoverRectangle := ⟨(21/320),(1051/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0450.certificate9002.rectangle,RoutedCases.Batch0450.certificate9003.rectangle,RoutedCases.Batch0450.certificate9005.rectangle,RoutedCases.Batch0450.certificate9007.rectangle,RoutedCases.Batch0450.certificate9009.rectangle,RoutedCases.Batch0450.certificate9010.rectangle,RoutedCases.Batch0450.certificate9011.rectangle,RoutedCases.Batch0450.certificate9012.rectangle,RoutedCases.Batch0450.certificate9013.rectangle,RoutedCases.Batch0450.certificate9014.rectangle,RoutedCases.Batch0450.certificate9015.rectangle,RoutedCases.Batch0450.certificate9016.rectangle,RoutedCases.Batch0450.certificate9017.rectangle,RoutedCases.Batch0450.certificate9018.rectangle,RoutedCases.Batch0450.certificate9019.rectangle,RoutedCases.Batch0451.certificate9020.rectangle,RoutedCases.Batch0451.certificate9021.rectangle,RoutedCases.Batch0451.certificate9022.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9002,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9003,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9005,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9007,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9009,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9011,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9012,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9013,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9018,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9020,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9021,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9022,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1051/16000),(263/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0450.certificate9004.rectangle,RoutedCases.Batch0450.certificate9006.rectangle,RoutedCases.Batch0450.certificate9008.rectangle,RoutedCases.Batch0450.certificate9009.rectangle,RoutedCases.Batch0450.certificate9010.rectangle,RoutedCases.Batch0450.certificate9011.rectangle,RoutedCases.Batch0450.certificate9012.rectangle,RoutedCases.Batch0450.certificate9013.rectangle,RoutedCases.Batch0450.certificate9014.rectangle,RoutedCases.Batch0450.certificate9015.rectangle,RoutedCases.Batch0450.certificate9016.rectangle,RoutedCases.Batch0450.certificate9017.rectangle,RoutedCases.Batch0450.certificate9018.rectangle,RoutedCases.Batch0450.certificate9019.rectangle,RoutedCases.Batch0451.certificate9020.rectangle,RoutedCases.Batch0451.certificate9021.rectangle,RoutedCases.Batch0451.certificate9022.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9004,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9006,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9008,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9009,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9010,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9011,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9012,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9013,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9014,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9015,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9016,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9017,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9018,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0450.sound9019,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9020,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9021,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0451.sound9022,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(21/320),(263/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source154
