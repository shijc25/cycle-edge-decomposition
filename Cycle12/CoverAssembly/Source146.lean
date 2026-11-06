import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0441
import Cycle12.RoutedCases.Batch0442

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source146

def strip0 : RatCoverRectangle := ⟨(517/8000),(207/3200),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0441.certificate8826.rectangle,RoutedCases.Batch0441.certificate8827.rectangle,RoutedCases.Batch0441.certificate8829.rectangle,RoutedCases.Batch0441.certificate8831.rectangle,RoutedCases.Batch0441.certificate8833.rectangle,RoutedCases.Batch0441.certificate8835.rectangle,RoutedCases.Batch0441.certificate8836.rectangle,RoutedCases.Batch0441.certificate8837.rectangle,RoutedCases.Batch0441.certificate8838.rectangle,RoutedCases.Batch0441.certificate8839.rectangle,RoutedCases.Batch0442.certificate8840.rectangle,RoutedCases.Batch0442.certificate8841.rectangle,RoutedCases.Batch0442.certificate8842.rectangle,RoutedCases.Batch0442.certificate8843.rectangle,RoutedCases.Batch0442.certificate8844.rectangle,RoutedCases.Batch0442.certificate8845.rectangle,RoutedCases.Batch0442.certificate8846.rectangle,RoutedCases.Batch0442.certificate8847.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8826,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8836,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8837,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8846,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8847,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(207/3200),(259/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0441.certificate8828.rectangle,RoutedCases.Batch0441.certificate8830.rectangle,RoutedCases.Batch0441.certificate8832.rectangle,RoutedCases.Batch0441.certificate8834.rectangle,RoutedCases.Batch0441.certificate8835.rectangle,RoutedCases.Batch0441.certificate8836.rectangle,RoutedCases.Batch0441.certificate8837.rectangle,RoutedCases.Batch0441.certificate8838.rectangle,RoutedCases.Batch0441.certificate8839.rectangle,RoutedCases.Batch0442.certificate8840.rectangle,RoutedCases.Batch0442.certificate8841.rectangle,RoutedCases.Batch0442.certificate8842.rectangle,RoutedCases.Batch0442.certificate8843.rectangle,RoutedCases.Batch0442.certificate8844.rectangle,RoutedCases.Batch0442.certificate8845.rectangle,RoutedCases.Batch0442.certificate8846.rectangle,RoutedCases.Batch0442.certificate8847.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8828,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8836,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8837,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0441.sound8839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8846,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8847,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(517/8000),(259/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source146
