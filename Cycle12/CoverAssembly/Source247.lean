import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0713

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source247

def strip0 : RatCoverRectangle := ⟨(3/400),(31/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14261.rectangle,RoutedCases.Batch0713.certificate14262.rectangle,RoutedCases.Batch0713.certificate14263.rectangle,RoutedCases.Batch0713.certificate14264.rectangle,RoutedCases.Batch0713.certificate14265.rectangle,RoutedCases.Batch0713.certificate14266.rectangle,RoutedCases.Batch0713.certificate14268.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14262,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14263,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14264,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14265,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14266,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14268,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(31/4000),(1/125),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0713.certificate14261.rectangle,RoutedCases.Batch0713.certificate14262.rectangle,RoutedCases.Batch0713.certificate14263.rectangle,RoutedCases.Batch0713.certificate14264.rectangle,RoutedCases.Batch0713.certificate14265.rectangle,RoutedCases.Batch0713.certificate14267.rectangle,RoutedCases.Batch0713.certificate14269.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14262,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14263,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14264,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14265,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14267,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14269,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/400),(1/125),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source247
