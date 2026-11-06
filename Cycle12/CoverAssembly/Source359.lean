import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0846
import Cycle12.RoutedCases.Batch0847

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source359

def strip0 : RatCoverRectangle := ⟨(3/125),(97/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0846.certificate16921.rectangle,RoutedCases.Batch0846.certificate16922.rectangle,RoutedCases.Batch0846.certificate16923.rectangle,RoutedCases.Batch0846.certificate16924.rectangle,RoutedCases.Batch0846.certificate16926.rectangle,RoutedCases.Batch0846.certificate16928.rectangle,RoutedCases.Batch0846.certificate16930.rectangle,RoutedCases.Batch0846.certificate16932.rectangle,RoutedCases.Batch0846.certificate16933.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16933,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(97/4000),(49/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0846.certificate16921.rectangle,RoutedCases.Batch0846.certificate16922.rectangle,RoutedCases.Batch0846.certificate16923.rectangle,RoutedCases.Batch0846.certificate16924.rectangle,RoutedCases.Batch0846.certificate16926.rectangle,RoutedCases.Batch0846.certificate16928.rectangle,RoutedCases.Batch0846.certificate16930.rectangle,RoutedCases.Batch0846.certificate16932.rectangle,RoutedCases.Batch0846.certificate16934.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16924,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16926,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16934,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(49/2000),(99/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0846.certificate16921.rectangle,RoutedCases.Batch0846.certificate16922.rectangle,RoutedCases.Batch0846.certificate16923.rectangle,RoutedCases.Batch0846.certificate16925.rectangle,RoutedCases.Batch0846.certificate16927.rectangle,RoutedCases.Batch0846.certificate16929.rectangle,RoutedCases.Batch0846.certificate16931.rectangle,RoutedCases.Batch0846.certificate16935.rectangle,RoutedCases.Batch0846.certificate16937.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16935,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16937,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(99/4000),(199/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0846.certificate16921.rectangle,RoutedCases.Batch0846.certificate16922.rectangle,RoutedCases.Batch0846.certificate16923.rectangle,RoutedCases.Batch0846.certificate16925.rectangle,RoutedCases.Batch0846.certificate16927.rectangle,RoutedCases.Batch0846.certificate16929.rectangle,RoutedCases.Batch0846.certificate16931.rectangle,RoutedCases.Batch0846.certificate16936.rectangle,RoutedCases.Batch0846.certificate16938.rectangle,RoutedCases.Batch0846.certificate16939.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16936,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16938,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16939,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(199/8000),(1/40),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0846.certificate16921.rectangle,RoutedCases.Batch0846.certificate16922.rectangle,RoutedCases.Batch0846.certificate16923.rectangle,RoutedCases.Batch0846.certificate16925.rectangle,RoutedCases.Batch0846.certificate16927.rectangle,RoutedCases.Batch0846.certificate16929.rectangle,RoutedCases.Batch0846.certificate16931.rectangle,RoutedCases.Batch0846.certificate16936.rectangle,RoutedCases.Batch0846.certificate16938.rectangle,RoutedCases.Batch0847.certificate16940.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16921,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16922,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16923,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16925,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16927,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16936,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16938,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0847.sound16940,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/125),(1/40),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source359
