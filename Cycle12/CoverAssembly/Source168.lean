import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0466
import Cycle12.RoutedCases.Batch0467
import Cycle12.RoutedCases.Batch0468

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source168

def strip0 : RatCoverRectangle := ⟨(1/250),(17/4000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0466.certificate9327.rectangle,RoutedCases.Batch0466.certificate9329.rectangle,RoutedCases.Batch0467.certificate9342.rectangle,RoutedCases.Batch0467.certificate9350.rectangle,RoutedCases.Batch0467.certificate9352.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9329,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9350,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9352,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(17/4000),(9/2000),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0466.certificate9328.rectangle,RoutedCases.Batch0466.certificate9330.rectangle,RoutedCases.Batch0467.certificate9343.rectangle,RoutedCases.Batch0467.certificate9351.rectangle,RoutedCases.Batch0467.certificate9353.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9328,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9330,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9343,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9351,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9353,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(9/2000),(19/4000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0466.certificate9331.rectangle,RoutedCases.Batch0466.certificate9332.rectangle,RoutedCases.Batch0466.certificate9337.rectangle,RoutedCases.Batch0467.certificate9344.rectangle,RoutedCases.Batch0467.certificate9345.rectangle,RoutedCases.Batch0467.certificate9354.rectangle,RoutedCases.Batch0467.certificate9355.rectangle,RoutedCases.Batch0468.certificate9360.rectangle,RoutedCases.Batch0468.certificate9361.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9331,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9332,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9337,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9345,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9354,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9355,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9360,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9361,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(19/4000),(39/8000),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0466.certificate9333.rectangle,RoutedCases.Batch0466.certificate9335.rectangle,RoutedCases.Batch0466.certificate9338.rectangle,RoutedCases.Batch0467.certificate9340.rectangle,RoutedCases.Batch0467.certificate9346.rectangle,RoutedCases.Batch0467.certificate9348.rectangle,RoutedCases.Batch0467.certificate9356.rectangle,RoutedCases.Batch0467.certificate9358.rectangle,RoutedCases.Batch0468.certificate9362.rectangle,RoutedCases.Batch0468.certificate9364.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9333,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9335,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9338,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9340,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9346,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9348,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9356,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9358,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9362,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9364,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(39/8000),(1/200),2,(some 5)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0466.certificate9334.rectangle,RoutedCases.Batch0466.certificate9336.rectangle,RoutedCases.Batch0466.certificate9339.rectangle,RoutedCases.Batch0467.certificate9341.rectangle,RoutedCases.Batch0467.certificate9347.rectangle,RoutedCases.Batch0467.certificate9349.rectangle,RoutedCases.Batch0467.certificate9357.rectangle,RoutedCases.Batch0467.certificate9359.rectangle,RoutedCases.Batch0468.certificate9363.rectangle,RoutedCases.Batch0468.certificate9365.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9334,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9336,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0466.sound9339,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9341,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9347,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9349,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9357,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0467.sound9359,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9363,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0468.sound9365,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/250),(1/200),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source168
