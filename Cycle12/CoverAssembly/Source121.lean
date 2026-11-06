import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0407
import Cycle12.RoutedCases.Batch0408

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source121

def strip0 : RatCoverRectangle := ⟨(243/4000),(487/8000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0407.certificate8156.rectangle,RoutedCases.Batch0407.certificate8158.rectangle,RoutedCases.Batch0408.certificate8160.rectangle,RoutedCases.Batch0408.certificate8161.rectangle,RoutedCases.Batch0408.certificate8162.rectangle,RoutedCases.Batch0408.certificate8163.rectangle,RoutedCases.Batch0408.certificate8164.rectangle,RoutedCases.Batch0408.certificate8165.rectangle,RoutedCases.Batch0408.certificate8166.rectangle,RoutedCases.Batch0408.certificate8167.rectangle,RoutedCases.Batch0408.certificate8168.rectangle,RoutedCases.Batch0408.certificate8169.rectangle,RoutedCases.Batch0408.certificate8170.rectangle,RoutedCases.Batch0408.certificate8171.rectangle,RoutedCases.Batch0408.certificate8172.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8156,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8158,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8160,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8161,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8162,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8163,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8164,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8165,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8166,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8167,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8168,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8169,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8170,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8171,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8172,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(487/8000),(61/1000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0407.certificate8157.rectangle,RoutedCases.Batch0407.certificate8159.rectangle,RoutedCases.Batch0408.certificate8160.rectangle,RoutedCases.Batch0408.certificate8161.rectangle,RoutedCases.Batch0408.certificate8162.rectangle,RoutedCases.Batch0408.certificate8163.rectangle,RoutedCases.Batch0408.certificate8164.rectangle,RoutedCases.Batch0408.certificate8165.rectangle,RoutedCases.Batch0408.certificate8166.rectangle,RoutedCases.Batch0408.certificate8167.rectangle,RoutedCases.Batch0408.certificate8168.rectangle,RoutedCases.Batch0408.certificate8169.rectangle,RoutedCases.Batch0408.certificate8170.rectangle,RoutedCases.Batch0408.certificate8171.rectangle,RoutedCases.Batch0408.certificate8172.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8157,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8159,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8160,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8161,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8162,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8163,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8164,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8165,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8166,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8167,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8168,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8169,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8170,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8171,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0408.sound8172,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(243/4000),(61/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source121
