import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0892
import Cycle12.RoutedCases.Batch0893

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source390

def strip0 : RatCoverRectangle := ⟨(27/500),(433/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0892.certificate17851.rectangle,RoutedCases.Batch0892.certificate17852.rectangle,RoutedCases.Batch0892.certificate17853.rectangle,RoutedCases.Batch0892.certificate17854.rectangle,RoutedCases.Batch0892.certificate17855.rectangle,RoutedCases.Batch0892.certificate17857.rectangle,RoutedCases.Batch0892.certificate17859.rectangle,RoutedCases.Batch0893.certificate17860.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17851,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17852,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17853,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17854,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17855,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17857,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17860,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(433/8000),(217/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0892.certificate17851.rectangle,RoutedCases.Batch0892.certificate17852.rectangle,RoutedCases.Batch0892.certificate17853.rectangle,RoutedCases.Batch0892.certificate17854.rectangle,RoutedCases.Batch0892.certificate17855.rectangle,RoutedCases.Batch0892.certificate17857.rectangle,RoutedCases.Batch0892.certificate17859.rectangle,RoutedCases.Batch0893.certificate17861.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17851,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17852,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17853,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17854,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17855,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17857,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17861,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(217/4000),(109/2000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0892.certificate17851.rectangle,RoutedCases.Batch0892.certificate17852.rectangle,RoutedCases.Batch0892.certificate17853.rectangle,RoutedCases.Batch0892.certificate17854.rectangle,RoutedCases.Batch0892.certificate17856.rectangle,RoutedCases.Batch0892.certificate17858.rectangle,RoutedCases.Batch0893.certificate17862.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17851,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17852,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17853,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17854,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17856,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17862,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(27/500),(109/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source390
