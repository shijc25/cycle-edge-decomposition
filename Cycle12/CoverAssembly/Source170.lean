import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0469
import Cycle12.RoutedCases.Batch0470

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source170

def strip0 : RatCoverRectangle := ⟨(3/500),(1/160),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0469.certificate9382.rectangle,RoutedCases.Batch0469.certificate9383.rectangle,RoutedCases.Batch0469.certificate9388.rectangle,RoutedCases.Batch0469.certificate9389.rectangle,RoutedCases.Batch0469.certificate9394.rectangle,RoutedCases.Batch0469.certificate9396.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9382,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9383,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9388,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9389,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9396,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1/160),(13/2000),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0469.certificate9382.rectangle,RoutedCases.Batch0469.certificate9383.rectangle,RoutedCases.Batch0469.certificate9388.rectangle,RoutedCases.Batch0469.certificate9389.rectangle,RoutedCases.Batch0469.certificate9395.rectangle,RoutedCases.Batch0469.certificate9397.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9382,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9383,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9388,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9389,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9397,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(13/2000),(27/4000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0469.certificate9384.rectangle,RoutedCases.Batch0469.certificate9386.rectangle,RoutedCases.Batch0469.certificate9390.rectangle,RoutedCases.Batch0469.certificate9392.rectangle,RoutedCases.Batch0469.certificate9398.rectangle,RoutedCases.Batch0470.certificate9401.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9384,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9386,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9390,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9398,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9401,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(27/4000),(7/1000),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0469.certificate9385.rectangle,RoutedCases.Batch0469.certificate9387.rectangle,RoutedCases.Batch0469.certificate9391.rectangle,RoutedCases.Batch0469.certificate9393.rectangle,RoutedCases.Batch0469.certificate9399.rectangle,RoutedCases.Batch0470.certificate9400.rectangle,RoutedCases.Batch0470.certificate9402.rectangle,RoutedCases.Batch0470.certificate9403.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9385,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9387,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9391,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0469.sound9399,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0470.sound9403,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/500),(7/1000),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source170
