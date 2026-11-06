import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0473
import Cycle12.RoutedCases.Batch0474
import Cycle12.RoutedCases.Batch0475

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source173

def strip0 : RatCoverRectangle := ⟨(9/1000),(37/4000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0473.certificate9470.rectangle,RoutedCases.Batch0473.certificate9475.rectangle,RoutedCases.Batch0474.certificate9480.rectangle,RoutedCases.Batch0474.certificate9481.rectangle,RoutedCases.Batch0474.certificate9486.rectangle,RoutedCases.Batch0474.certificate9487.rectangle,RoutedCases.Batch0474.certificate9493.rectangle,RoutedCases.Batch0474.certificate9495.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9470,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9475,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9486,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9493,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9495,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(37/4000),(19/2000),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0473.certificate9470.rectangle,RoutedCases.Batch0473.certificate9475.rectangle,RoutedCases.Batch0474.certificate9480.rectangle,RoutedCases.Batch0474.certificate9481.rectangle,RoutedCases.Batch0474.certificate9486.rectangle,RoutedCases.Batch0474.certificate9487.rectangle,RoutedCases.Batch0474.certificate9494.rectangle,RoutedCases.Batch0474.certificate9496.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9470,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9475,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9480,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9486,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9487,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9494,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9496,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(19/2000),(39/4000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0473.certificate9471.rectangle,RoutedCases.Batch0473.certificate9473.rectangle,RoutedCases.Batch0473.certificate9476.rectangle,RoutedCases.Batch0473.certificate9478.rectangle,RoutedCases.Batch0474.certificate9482.rectangle,RoutedCases.Batch0474.certificate9484.rectangle,RoutedCases.Batch0474.certificate9488.rectangle,RoutedCases.Batch0474.certificate9490.rectangle,RoutedCases.Batch0474.certificate9497.rectangle,RoutedCases.Batch0475.certificate9500.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9471,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9473,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9476,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9482,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9484,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9488,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9490,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9497,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0475.sound9500,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(39/4000),(1/100),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0473.certificate9472.rectangle,RoutedCases.Batch0473.certificate9474.rectangle,RoutedCases.Batch0473.certificate9477.rectangle,RoutedCases.Batch0473.certificate9479.rectangle,RoutedCases.Batch0474.certificate9483.rectangle,RoutedCases.Batch0474.certificate9485.rectangle,RoutedCases.Batch0474.certificate9489.rectangle,RoutedCases.Batch0474.certificate9491.rectangle,RoutedCases.Batch0474.certificate9492.rectangle,RoutedCases.Batch0474.certificate9498.rectangle,RoutedCases.Batch0474.certificate9499.rectangle,RoutedCases.Batch0475.certificate9501.rectangle,RoutedCases.Batch0475.certificate9502.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9472,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9474,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0473.sound9479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9483,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9485,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9489,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9491,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9492,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9498,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0474.sound9499,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0475.sound9501,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0475.sound9502,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/1000),(1/100),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source173
