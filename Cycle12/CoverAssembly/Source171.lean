import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0470
import Cycle12.RoutedCases.Batch0471
import Cycle12.RoutedCases.Batch0472

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source171

def strip0 : RatCoverRectangle := ⟨(7/1000),(29/4000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0470.certificate9404.rectangle,RoutedCases.Batch0470.certificate9406.rectangle,RoutedCases.Batch0470.certificate9414.rectangle,RoutedCases.Batch0470.certificate9416.rectangle,RoutedCases.Batch0471.certificate9424.rectangle,RoutedCases.Batch0471.certificate9426.rectangle,RoutedCases.Batch0471.certificate9438.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9404,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9406,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9414,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9416,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9424,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9426,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9438,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(29/4000),(3/400),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0470.certificate9405.rectangle,RoutedCases.Batch0470.certificate9407.rectangle,RoutedCases.Batch0470.certificate9415.rectangle,RoutedCases.Batch0470.certificate9417.rectangle,RoutedCases.Batch0471.certificate9425.rectangle,RoutedCases.Batch0471.certificate9427.rectangle,RoutedCases.Batch0471.certificate9439.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9405,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9407,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9415,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9417,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9425,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9427,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9439,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(3/400),(31/4000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0470.certificate9408.rectangle,RoutedCases.Batch0470.certificate9411.rectangle,RoutedCases.Batch0470.certificate9418.rectangle,RoutedCases.Batch0471.certificate9421.rectangle,RoutedCases.Batch0471.certificate9428.rectangle,RoutedCases.Batch0471.certificate9433.rectangle,RoutedCases.Batch0472.certificate9440.rectangle,RoutedCases.Batch0472.certificate9441.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9408,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9411,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9418,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9421,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9428,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9433,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9440,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9441,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(31/4000),(63/8000),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0470.certificate9409.rectangle,RoutedCases.Batch0470.certificate9410.rectangle,RoutedCases.Batch0470.certificate9412.rectangle,RoutedCases.Batch0470.certificate9413.rectangle,RoutedCases.Batch0470.certificate9419.rectangle,RoutedCases.Batch0471.certificate9420.rectangle,RoutedCases.Batch0471.certificate9422.rectangle,RoutedCases.Batch0471.certificate9423.rectangle,RoutedCases.Batch0471.certificate9429.rectangle,RoutedCases.Batch0471.certificate9431.rectangle,RoutedCases.Batch0471.certificate9434.rectangle,RoutedCases.Batch0471.certificate9436.rectangle,RoutedCases.Batch0472.certificate9442.rectangle,RoutedCases.Batch0472.certificate9445.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9409,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9410,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9412,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9413,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9419,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9420,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9422,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9423,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9429,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9431,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9434,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9442,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9445,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(63/8000),(1/125),2,(some 5)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0470.certificate9409.rectangle,RoutedCases.Batch0470.certificate9410.rectangle,RoutedCases.Batch0470.certificate9412.rectangle,RoutedCases.Batch0470.certificate9413.rectangle,RoutedCases.Batch0470.certificate9419.rectangle,RoutedCases.Batch0471.certificate9420.rectangle,RoutedCases.Batch0471.certificate9422.rectangle,RoutedCases.Batch0471.certificate9423.rectangle,RoutedCases.Batch0471.certificate9430.rectangle,RoutedCases.Batch0471.certificate9432.rectangle,RoutedCases.Batch0471.certificate9435.rectangle,RoutedCases.Batch0471.certificate9437.rectangle,RoutedCases.Batch0472.certificate9443.rectangle,RoutedCases.Batch0472.certificate9444.rectangle,RoutedCases.Batch0472.certificate9446.rectangle,RoutedCases.Batch0472.certificate9447.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9409,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9410,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9412,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9413,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9419,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9420,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9422,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9423,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9430,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9432,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0471.sound9437,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9443,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9444,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9446,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0472.sound9447,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/1000),(1/125),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source171
