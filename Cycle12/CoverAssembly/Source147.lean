import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0442
import Cycle12.RoutedCases.Batch0443

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source147

def strip0 : RatCoverRectangle := ⟨(259/4000),(1037/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0442.certificate8848.rectangle,RoutedCases.Batch0442.certificate8849.rectangle,RoutedCases.Batch0442.certificate8851.rectangle,RoutedCases.Batch0442.certificate8853.rectangle,RoutedCases.Batch0442.certificate8855.rectangle,RoutedCases.Batch0442.certificate8857.rectangle,RoutedCases.Batch0442.certificate8858.rectangle,RoutedCases.Batch0442.certificate8859.rectangle,RoutedCases.Batch0443.certificate8860.rectangle,RoutedCases.Batch0443.certificate8861.rectangle,RoutedCases.Batch0443.certificate8862.rectangle,RoutedCases.Batch0443.certificate8863.rectangle,RoutedCases.Batch0443.certificate8864.rectangle,RoutedCases.Batch0443.certificate8865.rectangle,RoutedCases.Batch0443.certificate8866.rectangle,RoutedCases.Batch0443.certificate8867.rectangle,RoutedCases.Batch0443.certificate8868.rectangle,RoutedCases.Batch0443.certificate8869.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8848,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8849,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8851,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8853,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8855,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8857,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8861,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8862,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8863,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8869,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1037/16000),(519/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0442.certificate8850.rectangle,RoutedCases.Batch0442.certificate8852.rectangle,RoutedCases.Batch0442.certificate8854.rectangle,RoutedCases.Batch0442.certificate8856.rectangle,RoutedCases.Batch0442.certificate8857.rectangle,RoutedCases.Batch0442.certificate8858.rectangle,RoutedCases.Batch0442.certificate8859.rectangle,RoutedCases.Batch0443.certificate8860.rectangle,RoutedCases.Batch0443.certificate8861.rectangle,RoutedCases.Batch0443.certificate8862.rectangle,RoutedCases.Batch0443.certificate8863.rectangle,RoutedCases.Batch0443.certificate8864.rectangle,RoutedCases.Batch0443.certificate8865.rectangle,RoutedCases.Batch0443.certificate8866.rectangle,RoutedCases.Batch0443.certificate8867.rectangle,RoutedCases.Batch0443.certificate8868.rectangle,RoutedCases.Batch0443.certificate8869.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8850,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8852,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8854,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8856,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8857,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0442.sound8859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8861,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8862,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8863,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0443.sound8869,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(259/4000),(519/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source147
