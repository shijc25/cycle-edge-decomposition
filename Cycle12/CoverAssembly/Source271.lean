import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0746
import Cycle12.RoutedCases.Batch0747

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source271

def strip0 : RatCoverRectangle := ⟨(3/100),(121/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0746.certificate14920.rectangle,RoutedCases.Batch0746.certificate14921.rectangle,RoutedCases.Batch0746.certificate14922.rectangle,RoutedCases.Batch0746.certificate14923.rectangle,RoutedCases.Batch0746.certificate14924.rectangle,RoutedCases.Batch0746.certificate14925.rectangle,RoutedCases.Batch0746.certificate14926.rectangle,RoutedCases.Batch0746.certificate14928.rectangle,RoutedCases.Batch0746.certificate14930.rectangle,RoutedCases.Batch0746.certificate14932.rectangle,RoutedCases.Batch0746.certificate14935.rectangle,RoutedCases.Batch0746.certificate14936.rectangle,RoutedCases.Batch0747.certificate14942.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14920,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14935,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14936,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14942,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(121/4000),(61/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0746.certificate14920.rectangle,RoutedCases.Batch0746.certificate14921.rectangle,RoutedCases.Batch0746.certificate14922.rectangle,RoutedCases.Batch0746.certificate14923.rectangle,RoutedCases.Batch0746.certificate14924.rectangle,RoutedCases.Batch0746.certificate14925.rectangle,RoutedCases.Batch0746.certificate14926.rectangle,RoutedCases.Batch0746.certificate14928.rectangle,RoutedCases.Batch0746.certificate14930.rectangle,RoutedCases.Batch0746.certificate14932.rectangle,RoutedCases.Batch0746.certificate14935.rectangle,RoutedCases.Batch0746.certificate14937.rectangle,RoutedCases.Batch0747.certificate14943.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14920,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14935,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14937,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14943,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(61/2000),(123/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0746.certificate14920.rectangle,RoutedCases.Batch0746.certificate14921.rectangle,RoutedCases.Batch0746.certificate14922.rectangle,RoutedCases.Batch0746.certificate14923.rectangle,RoutedCases.Batch0746.certificate14924.rectangle,RoutedCases.Batch0746.certificate14925.rectangle,RoutedCases.Batch0746.certificate14927.rectangle,RoutedCases.Batch0746.certificate14929.rectangle,RoutedCases.Batch0746.certificate14931.rectangle,RoutedCases.Batch0746.certificate14933.rectangle,RoutedCases.Batch0746.certificate14934.rectangle,RoutedCases.Batch0746.certificate14938.rectangle,RoutedCases.Batch0747.certificate14940.rectangle,RoutedCases.Batch0747.certificate14944.rectangle,RoutedCases.Batch0747.certificate14946.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14920,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14933,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14934,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14938,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14940,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14946,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(123/4000),(31/1000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0746.certificate14920.rectangle,RoutedCases.Batch0746.certificate14921.rectangle,RoutedCases.Batch0746.certificate14922.rectangle,RoutedCases.Batch0746.certificate14923.rectangle,RoutedCases.Batch0746.certificate14924.rectangle,RoutedCases.Batch0746.certificate14925.rectangle,RoutedCases.Batch0746.certificate14927.rectangle,RoutedCases.Batch0746.certificate14929.rectangle,RoutedCases.Batch0746.certificate14931.rectangle,RoutedCases.Batch0746.certificate14933.rectangle,RoutedCases.Batch0746.certificate14934.rectangle,RoutedCases.Batch0746.certificate14939.rectangle,RoutedCases.Batch0747.certificate14941.rectangle,RoutedCases.Batch0747.certificate14945.rectangle,RoutedCases.Batch0747.certificate14947.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14920,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14933,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14934,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0746.sound14939,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0747.sound14947,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/100),(31/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source271
