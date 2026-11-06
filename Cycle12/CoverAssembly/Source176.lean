import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0479
import Cycle12.RoutedCases.Batch0480

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source176

def strip0 : RatCoverRectangle := ⟨(3/250),(49/4000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0479.certificate9583.rectangle,RoutedCases.Batch0479.certificate9586.rectangle,RoutedCases.Batch0479.certificate9589.rectangle,RoutedCases.Batch0479.certificate9592.rectangle,RoutedCases.Batch0479.certificate9596.rectangle,RoutedCases.Batch0479.certificate9597.rectangle,RoutedCases.Batch0480.certificate9602.rectangle,RoutedCases.Batch0480.certificate9604.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9583,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9586,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9597,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9604,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(49/4000),(1/80),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0479.certificate9583.rectangle,RoutedCases.Batch0479.certificate9586.rectangle,RoutedCases.Batch0479.certificate9589.rectangle,RoutedCases.Batch0479.certificate9592.rectangle,RoutedCases.Batch0479.certificate9596.rectangle,RoutedCases.Batch0479.certificate9597.rectangle,RoutedCases.Batch0480.certificate9603.rectangle,RoutedCases.Batch0480.certificate9605.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9583,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9586,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9597,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9603,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9605,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(1/80),(51/4000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0479.certificate9584.rectangle,RoutedCases.Batch0479.certificate9585.rectangle,RoutedCases.Batch0479.certificate9587.rectangle,RoutedCases.Batch0479.certificate9588.rectangle,RoutedCases.Batch0479.certificate9590.rectangle,RoutedCases.Batch0479.certificate9591.rectangle,RoutedCases.Batch0479.certificate9593.rectangle,RoutedCases.Batch0479.certificate9594.rectangle,RoutedCases.Batch0479.certificate9598.rectangle,RoutedCases.Batch0480.certificate9600.rectangle,RoutedCases.Batch0480.certificate9606.rectangle,RoutedCases.Batch0480.certificate9608.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9584,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9585,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9587,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9588,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9591,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9593,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9598,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9608,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(51/4000),(13/1000),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0479.certificate9584.rectangle,RoutedCases.Batch0479.certificate9585.rectangle,RoutedCases.Batch0479.certificate9587.rectangle,RoutedCases.Batch0479.certificate9588.rectangle,RoutedCases.Batch0479.certificate9590.rectangle,RoutedCases.Batch0479.certificate9591.rectangle,RoutedCases.Batch0479.certificate9593.rectangle,RoutedCases.Batch0479.certificate9595.rectangle,RoutedCases.Batch0479.certificate9599.rectangle,RoutedCases.Batch0480.certificate9601.rectangle,RoutedCases.Batch0480.certificate9607.rectangle,RoutedCases.Batch0480.certificate9609.rectangle,RoutedCases.Batch0480.certificate9610.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9584,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9585,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9587,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9588,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9591,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9593,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9595,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0480.sound9610,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/250),(13/1000),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source176
