import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0435
import Cycle12.RoutedCases.Batch0436

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source141

def strip0 : RatCoverRectangle := ⟨(8/125),(41/640),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0435.certificate8719.rectangle,RoutedCases.Batch0436.certificate8721.rectangle,RoutedCases.Batch0436.certificate8723.rectangle,RoutedCases.Batch0436.certificate8725.rectangle,RoutedCases.Batch0436.certificate8726.rectangle,RoutedCases.Batch0436.certificate8727.rectangle,RoutedCases.Batch0436.certificate8728.rectangle,RoutedCases.Batch0436.certificate8729.rectangle,RoutedCases.Batch0436.certificate8730.rectangle,RoutedCases.Batch0436.certificate8731.rectangle,RoutedCases.Batch0436.certificate8732.rectangle,RoutedCases.Batch0436.certificate8733.rectangle,RoutedCases.Batch0436.certificate8734.rectangle,RoutedCases.Batch0436.certificate8735.rectangle,RoutedCases.Batch0436.certificate8736.rectangle,RoutedCases.Batch0436.certificate8737.rectangle,RoutedCases.Batch0436.certificate8738.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0435.sound8719,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8721,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8723,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8725,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8726,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8727,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8728,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8729,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8738,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(41/640),(513/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0436.certificate8720.rectangle,RoutedCases.Batch0436.certificate8722.rectangle,RoutedCases.Batch0436.certificate8724.rectangle,RoutedCases.Batch0436.certificate8725.rectangle,RoutedCases.Batch0436.certificate8726.rectangle,RoutedCases.Batch0436.certificate8727.rectangle,RoutedCases.Batch0436.certificate8728.rectangle,RoutedCases.Batch0436.certificate8729.rectangle,RoutedCases.Batch0436.certificate8730.rectangle,RoutedCases.Batch0436.certificate8731.rectangle,RoutedCases.Batch0436.certificate8732.rectangle,RoutedCases.Batch0436.certificate8733.rectangle,RoutedCases.Batch0436.certificate8734.rectangle,RoutedCases.Batch0436.certificate8735.rectangle,RoutedCases.Batch0436.certificate8736.rectangle,RoutedCases.Batch0436.certificate8737.rectangle,RoutedCases.Batch0436.certificate8738.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8720,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8722,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8724,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8725,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8726,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8727,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8728,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8729,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0436.sound8738,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(8/125),(513/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source141
