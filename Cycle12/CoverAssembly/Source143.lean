import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0438
import Cycle12.RoutedCases.Batch0439

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source143

def strip0 : RatCoverRectangle := ⟨(257/4000),(1029/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0438.certificate8760.rectangle,RoutedCases.Batch0438.certificate8761.rectangle,RoutedCases.Batch0438.certificate8763.rectangle,RoutedCases.Batch0438.certificate8765.rectangle,RoutedCases.Batch0438.certificate8767.rectangle,RoutedCases.Batch0438.certificate8769.rectangle,RoutedCases.Batch0438.certificate8770.rectangle,RoutedCases.Batch0438.certificate8771.rectangle,RoutedCases.Batch0438.certificate8772.rectangle,RoutedCases.Batch0438.certificate8773.rectangle,RoutedCases.Batch0438.certificate8774.rectangle,RoutedCases.Batch0438.certificate8775.rectangle,RoutedCases.Batch0438.certificate8776.rectangle,RoutedCases.Batch0438.certificate8777.rectangle,RoutedCases.Batch0438.certificate8778.rectangle,RoutedCases.Batch0438.certificate8779.rectangle,RoutedCases.Batch0439.certificate8780.rectangle,RoutedCases.Batch0439.certificate8781.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8760,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8761,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8763,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8765,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8767,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8769,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8772,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8773,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8774,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8775,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8776,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8777,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8778,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8779,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8781,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1029/16000),(103/1600),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0438.certificate8762.rectangle,RoutedCases.Batch0438.certificate8764.rectangle,RoutedCases.Batch0438.certificate8766.rectangle,RoutedCases.Batch0438.certificate8768.rectangle,RoutedCases.Batch0438.certificate8769.rectangle,RoutedCases.Batch0438.certificate8770.rectangle,RoutedCases.Batch0438.certificate8771.rectangle,RoutedCases.Batch0438.certificate8772.rectangle,RoutedCases.Batch0438.certificate8773.rectangle,RoutedCases.Batch0438.certificate8774.rectangle,RoutedCases.Batch0438.certificate8775.rectangle,RoutedCases.Batch0438.certificate8776.rectangle,RoutedCases.Batch0438.certificate8777.rectangle,RoutedCases.Batch0438.certificate8778.rectangle,RoutedCases.Batch0438.certificate8779.rectangle,RoutedCases.Batch0439.certificate8780.rectangle,RoutedCases.Batch0439.certificate8781.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8762,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8764,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8766,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8768,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8769,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8772,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8773,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8774,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8775,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8776,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8777,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8778,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0438.sound8779,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8781,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(257/4000),(103/1600),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source143
