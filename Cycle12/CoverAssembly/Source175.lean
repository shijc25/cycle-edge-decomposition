import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0477
import Cycle12.RoutedCases.Batch0478
import Cycle12.RoutedCases.Batch0479

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source175

def strip0 : RatCoverRectangle := ⟨(11/1000),(23/2000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0477.certificate9559.rectangle,RoutedCases.Batch0478.certificate9562.rectangle,RoutedCases.Batch0478.certificate9565.rectangle,RoutedCases.Batch0478.certificate9568.rectangle,RoutedCases.Batch0478.certificate9571.rectangle,RoutedCases.Batch0478.certificate9572.rectangle,RoutedCases.Batch0478.certificate9577.rectangle,RoutedCases.Batch0478.certificate9578.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0477.sound9559,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9562,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9565,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9568,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9571,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9578,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(23/2000),(47/4000),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0478.certificate9560.rectangle,RoutedCases.Batch0478.certificate9561.rectangle,RoutedCases.Batch0478.certificate9563.rectangle,RoutedCases.Batch0478.certificate9564.rectangle,RoutedCases.Batch0478.certificate9566.rectangle,RoutedCases.Batch0478.certificate9567.rectangle,RoutedCases.Batch0478.certificate9569.rectangle,RoutedCases.Batch0478.certificate9573.rectangle,RoutedCases.Batch0478.certificate9575.rectangle,RoutedCases.Batch0478.certificate9579.rectangle,RoutedCases.Batch0479.certificate9581.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9560,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9561,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9563,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9564,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9566,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9567,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9569,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9581,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(47/4000),(3/250),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0478.certificate9560.rectangle,RoutedCases.Batch0478.certificate9561.rectangle,RoutedCases.Batch0478.certificate9563.rectangle,RoutedCases.Batch0478.certificate9564.rectangle,RoutedCases.Batch0478.certificate9566.rectangle,RoutedCases.Batch0478.certificate9567.rectangle,RoutedCases.Batch0478.certificate9570.rectangle,RoutedCases.Batch0478.certificate9574.rectangle,RoutedCases.Batch0478.certificate9576.rectangle,RoutedCases.Batch0479.certificate9580.rectangle,RoutedCases.Batch0479.certificate9582.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9560,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9561,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9563,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9564,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9566,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9567,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9570,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0478.sound9576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0479.sound9582,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/1000),(3/250),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source175
