import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0716
import Cycle12.RoutedCases.Batch0717

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source250

def strip0 : RatCoverRectangle := ⟨(1/100),(21/2000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0716.certificate14326.rectangle,RoutedCases.Batch0716.certificate14327.rectangle,RoutedCases.Batch0716.certificate14328.rectangle,RoutedCases.Batch0716.certificate14330.rectangle,RoutedCases.Batch0716.certificate14332.rectangle,RoutedCases.Batch0716.certificate14334.rectangle,RoutedCases.Batch0716.certificate14336.rectangle,RoutedCases.Batch0716.certificate14339.rectangle,RoutedCases.Batch0717.certificate14340.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14326,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14328,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14330,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14332,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14334,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14336,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14339,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14340,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(21/2000),(43/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0716.certificate14326.rectangle,RoutedCases.Batch0716.certificate14327.rectangle,RoutedCases.Batch0716.certificate14329.rectangle,RoutedCases.Batch0716.certificate14331.rectangle,RoutedCases.Batch0716.certificate14333.rectangle,RoutedCases.Batch0716.certificate14335.rectangle,RoutedCases.Batch0716.certificate14337.rectangle,RoutedCases.Batch0717.certificate14341.rectangle,RoutedCases.Batch0717.certificate14343.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14326,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14329,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14331,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14333,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14335,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14337,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14341,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14343,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(43/4000),(87/8000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0716.certificate14326.rectangle,RoutedCases.Batch0716.certificate14327.rectangle,RoutedCases.Batch0716.certificate14329.rectangle,RoutedCases.Batch0716.certificate14331.rectangle,RoutedCases.Batch0716.certificate14333.rectangle,RoutedCases.Batch0716.certificate14335.rectangle,RoutedCases.Batch0716.certificate14338.rectangle,RoutedCases.Batch0717.certificate14342.rectangle,RoutedCases.Batch0717.certificate14344.rectangle,RoutedCases.Batch0717.certificate14345.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14326,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14329,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14331,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14333,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14335,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14338,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14345,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(87/8000),(11/1000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0716.certificate14326.rectangle,RoutedCases.Batch0716.certificate14327.rectangle,RoutedCases.Batch0716.certificate14329.rectangle,RoutedCases.Batch0716.certificate14331.rectangle,RoutedCases.Batch0716.certificate14333.rectangle,RoutedCases.Batch0716.certificate14335.rectangle,RoutedCases.Batch0716.certificate14338.rectangle,RoutedCases.Batch0717.certificate14342.rectangle,RoutedCases.Batch0717.certificate14344.rectangle,RoutedCases.Batch0717.certificate14346.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14326,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14327,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14329,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14331,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14333,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14335,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14338,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14342,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14344,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14346,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/100),(11/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source250
