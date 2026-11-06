import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0312
import Cycle12.RoutedCases.Batch0313

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source082

def strip0 : RatCoverRectangle := ⟨(203/4000),(51/1000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0312.certificate6253.rectangle,RoutedCases.Batch0312.certificate6254.rectangle,RoutedCases.Batch0312.certificate6255.rectangle,RoutedCases.Batch0312.certificate6256.rectangle,RoutedCases.Batch0312.certificate6257.rectangle,RoutedCases.Batch0312.certificate6258.rectangle,RoutedCases.Batch0312.certificate6259.rectangle,RoutedCases.Batch0313.certificate6260.rectangle,RoutedCases.Batch0313.certificate6261.rectangle,RoutedCases.Batch0313.certificate6262.rectangle,RoutedCases.Batch0313.certificate6263.rectangle,RoutedCases.Batch0313.certificate6264.rectangle,RoutedCases.Batch0313.certificate6265.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6259,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0313.sound6260,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0313.sound6261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0313.sound6262,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0313.sound6263,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0313.sound6264,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0313.sound6265,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(203/4000),(51/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source082
