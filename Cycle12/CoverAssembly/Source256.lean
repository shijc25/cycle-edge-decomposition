import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0722
import Cycle12.RoutedCases.Batch0723
import Cycle12.RoutedCases.Batch0724

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source256

def strip0 : RatCoverRectangle := ⟨(3/200),(61/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0722.certificate14458.rectangle,RoutedCases.Batch0722.certificate14459.rectangle,RoutedCases.Batch0723.certificate14460.rectangle,RoutedCases.Batch0723.certificate14461.rectangle,RoutedCases.Batch0723.certificate14462.rectangle,RoutedCases.Batch0723.certificate14464.rectangle,RoutedCases.Batch0723.certificate14466.rectangle,RoutedCases.Batch0723.certificate14469.rectangle,RoutedCases.Batch0723.certificate14474.rectangle,RoutedCases.Batch0723.certificate14475.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14462,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14464,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14466,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14469,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14474,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14475,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(61/4000),(31/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0722.certificate14458.rectangle,RoutedCases.Batch0722.certificate14459.rectangle,RoutedCases.Batch0723.certificate14460.rectangle,RoutedCases.Batch0723.certificate14461.rectangle,RoutedCases.Batch0723.certificate14462.rectangle,RoutedCases.Batch0723.certificate14464.rectangle,RoutedCases.Batch0723.certificate14466.rectangle,RoutedCases.Batch0723.certificate14469.rectangle,RoutedCases.Batch0723.certificate14474.rectangle,RoutedCases.Batch0723.certificate14476.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14462,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14464,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14466,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14469,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14474,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14476,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(31/2000),(63/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0722.certificate14458.rectangle,RoutedCases.Batch0722.certificate14459.rectangle,RoutedCases.Batch0723.certificate14460.rectangle,RoutedCases.Batch0723.certificate14461.rectangle,RoutedCases.Batch0723.certificate14463.rectangle,RoutedCases.Batch0723.certificate14465.rectangle,RoutedCases.Batch0723.certificate14467.rectangle,RoutedCases.Batch0723.certificate14468.rectangle,RoutedCases.Batch0723.certificate14470.rectangle,RoutedCases.Batch0723.certificate14472.rectangle,RoutedCases.Batch0723.certificate14477.rectangle,RoutedCases.Batch0723.certificate14479.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14463,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14465,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14467,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14468,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14470,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14472,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14479,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(63/4000),(127/8000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0722.certificate14458.rectangle,RoutedCases.Batch0722.certificate14459.rectangle,RoutedCases.Batch0723.certificate14460.rectangle,RoutedCases.Batch0723.certificate14461.rectangle,RoutedCases.Batch0723.certificate14463.rectangle,RoutedCases.Batch0723.certificate14465.rectangle,RoutedCases.Batch0723.certificate14467.rectangle,RoutedCases.Batch0723.certificate14468.rectangle,RoutedCases.Batch0723.certificate14471.rectangle,RoutedCases.Batch0723.certificate14473.rectangle,RoutedCases.Batch0723.certificate14478.rectangle,RoutedCases.Batch0724.certificate14480.rectangle,RoutedCases.Batch0724.certificate14481.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14463,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14465,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14467,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14468,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14471,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14473,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0724.sound14480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0724.sound14481,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(127/8000),(2/125),5,(some 20)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0722.certificate14458.rectangle,RoutedCases.Batch0722.certificate14459.rectangle,RoutedCases.Batch0723.certificate14460.rectangle,RoutedCases.Batch0723.certificate14461.rectangle,RoutedCases.Batch0723.certificate14463.rectangle,RoutedCases.Batch0723.certificate14465.rectangle,RoutedCases.Batch0723.certificate14467.rectangle,RoutedCases.Batch0723.certificate14468.rectangle,RoutedCases.Batch0723.certificate14471.rectangle,RoutedCases.Batch0723.certificate14473.rectangle,RoutedCases.Batch0723.certificate14478.rectangle,RoutedCases.Batch0724.certificate14480.rectangle,RoutedCases.Batch0724.certificate14482.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0722.sound14459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14463,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14465,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14467,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14468,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14471,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14473,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0723.sound14478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0724.sound14480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0724.sound14482,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/200),(2/125),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source256
