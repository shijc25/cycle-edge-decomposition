import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0431
import Cycle12.RoutedCases.Batch0432

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source137

def strip0 : RatCoverRectangle := ⟨(127/2000),(1017/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0431.certificate8626.rectangle,RoutedCases.Batch0431.certificate8627.rectangle,RoutedCases.Batch0431.certificate8629.rectangle,RoutedCases.Batch0431.certificate8631.rectangle,RoutedCases.Batch0431.certificate8633.rectangle,RoutedCases.Batch0431.certificate8635.rectangle,RoutedCases.Batch0431.certificate8636.rectangle,RoutedCases.Batch0431.certificate8637.rectangle,RoutedCases.Batch0431.certificate8638.rectangle,RoutedCases.Batch0431.certificate8639.rectangle,RoutedCases.Batch0432.certificate8640.rectangle,RoutedCases.Batch0432.certificate8641.rectangle,RoutedCases.Batch0432.certificate8642.rectangle,RoutedCases.Batch0432.certificate8643.rectangle,RoutedCases.Batch0432.certificate8644.rectangle,RoutedCases.Batch0432.certificate8645.rectangle,RoutedCases.Batch0432.certificate8646.rectangle,RoutedCases.Batch0432.certificate8647.rectangle,RoutedCases.Batch0432.certificate8648.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8626,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8627,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8647,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8648,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1017/16000),(509/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0431.certificate8628.rectangle,RoutedCases.Batch0431.certificate8630.rectangle,RoutedCases.Batch0431.certificate8632.rectangle,RoutedCases.Batch0431.certificate8634.rectangle,RoutedCases.Batch0431.certificate8635.rectangle,RoutedCases.Batch0431.certificate8636.rectangle,RoutedCases.Batch0431.certificate8637.rectangle,RoutedCases.Batch0431.certificate8638.rectangle,RoutedCases.Batch0431.certificate8639.rectangle,RoutedCases.Batch0432.certificate8640.rectangle,RoutedCases.Batch0432.certificate8641.rectangle,RoutedCases.Batch0432.certificate8642.rectangle,RoutedCases.Batch0432.certificate8643.rectangle,RoutedCases.Batch0432.certificate8644.rectangle,RoutedCases.Batch0432.certificate8645.rectangle,RoutedCases.Batch0432.certificate8646.rectangle,RoutedCases.Batch0432.certificate8647.rectangle,RoutedCases.Batch0432.certificate8648.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8628,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0431.sound8639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8647,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0432.sound8648,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(127/2000),(509/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source137
