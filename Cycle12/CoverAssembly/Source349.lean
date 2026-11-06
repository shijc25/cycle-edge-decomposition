import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0838
import Cycle12.RoutedCases.Batch0839

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source349

def strip0 : RatCoverRectangle := ⟨(17/1000),(69/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0838.certificate16770.rectangle,RoutedCases.Batch0838.certificate16771.rectangle,RoutedCases.Batch0838.certificate16772.rectangle,RoutedCases.Batch0838.certificate16774.rectangle,RoutedCases.Batch0838.certificate16776.rectangle,RoutedCases.Batch0839.certificate16781.rectangle,RoutedCases.Batch0839.certificate16782.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16772,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16774,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16776,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16781,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16782,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(69/4000),(7/400),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0838.certificate16770.rectangle,RoutedCases.Batch0838.certificate16771.rectangle,RoutedCases.Batch0838.certificate16772.rectangle,RoutedCases.Batch0838.certificate16774.rectangle,RoutedCases.Batch0838.certificate16776.rectangle,RoutedCases.Batch0839.certificate16781.rectangle,RoutedCases.Batch0839.certificate16783.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16772,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16774,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16776,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16781,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16783,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(7/400),(71/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0838.certificate16770.rectangle,RoutedCases.Batch0838.certificate16771.rectangle,RoutedCases.Batch0838.certificate16773.rectangle,RoutedCases.Batch0838.certificate16775.rectangle,RoutedCases.Batch0838.certificate16777.rectangle,RoutedCases.Batch0838.certificate16779.rectangle,RoutedCases.Batch0839.certificate16784.rectangle,RoutedCases.Batch0839.certificate16786.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16773,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16775,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16777,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16779,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16784,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16786,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(71/4000),(143/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0838.certificate16770.rectangle,RoutedCases.Batch0838.certificate16771.rectangle,RoutedCases.Batch0838.certificate16773.rectangle,RoutedCases.Batch0838.certificate16775.rectangle,RoutedCases.Batch0838.certificate16778.rectangle,RoutedCases.Batch0839.certificate16780.rectangle,RoutedCases.Batch0839.certificate16785.rectangle,RoutedCases.Batch0839.certificate16787.rectangle,RoutedCases.Batch0839.certificate16789.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16773,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16775,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16778,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16785,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16787,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16789,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(143/8000),(9/500),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0838.certificate16770.rectangle,RoutedCases.Batch0838.certificate16771.rectangle,RoutedCases.Batch0838.certificate16773.rectangle,RoutedCases.Batch0838.certificate16775.rectangle,RoutedCases.Batch0838.certificate16778.rectangle,RoutedCases.Batch0839.certificate16780.rectangle,RoutedCases.Batch0839.certificate16785.rectangle,RoutedCases.Batch0839.certificate16788.rectangle,RoutedCases.Batch0839.certificate16790.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16773,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16775,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16778,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16780,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16785,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16788,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0839.sound16790,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(17/1000),(9/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source349
