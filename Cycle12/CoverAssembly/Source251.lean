import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0717

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source251

def strip0 : RatCoverRectangle := ⟨(11/1000),(9/800),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0717.certificate14347.rectangle,RoutedCases.Batch0717.certificate14348.rectangle,RoutedCases.Batch0717.certificate14349.rectangle,RoutedCases.Batch0717.certificate14350.rectangle,RoutedCases.Batch0717.certificate14352.rectangle,RoutedCases.Batch0717.certificate14354.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14348,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14349,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14350,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14352,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14354,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(9/800),(23/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0717.certificate14347.rectangle,RoutedCases.Batch0717.certificate14348.rectangle,RoutedCases.Batch0717.certificate14349.rectangle,RoutedCases.Batch0717.certificate14351.rectangle,RoutedCases.Batch0717.certificate14353.rectangle,RoutedCases.Batch0717.certificate14355.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14348,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14349,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14351,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14353,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14355,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/1000),(23/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source251
