import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0741
import Cycle12.RoutedCases.Batch0742

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source268

def strip0 : RatCoverRectangle := ⟨(27/1000),(109/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0741.certificate14829.rectangle,RoutedCases.Batch0741.certificate14830.rectangle,RoutedCases.Batch0741.certificate14831.rectangle,RoutedCases.Batch0741.certificate14832.rectangle,RoutedCases.Batch0741.certificate14833.rectangle,RoutedCases.Batch0741.certificate14834.rectangle,RoutedCases.Batch0741.certificate14835.rectangle,RoutedCases.Batch0741.certificate14837.rectangle,RoutedCases.Batch0741.certificate14839.rectangle,RoutedCases.Batch0742.certificate14841.rectangle,RoutedCases.Batch0742.certificate14844.rectangle,RoutedCases.Batch0742.certificate14845.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14837,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14845,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(109/4000),(11/400),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0741.certificate14829.rectangle,RoutedCases.Batch0741.certificate14830.rectangle,RoutedCases.Batch0741.certificate14831.rectangle,RoutedCases.Batch0741.certificate14832.rectangle,RoutedCases.Batch0741.certificate14833.rectangle,RoutedCases.Batch0741.certificate14834.rectangle,RoutedCases.Batch0741.certificate14835.rectangle,RoutedCases.Batch0741.certificate14837.rectangle,RoutedCases.Batch0741.certificate14839.rectangle,RoutedCases.Batch0742.certificate14841.rectangle,RoutedCases.Batch0742.certificate14844.rectangle,RoutedCases.Batch0742.certificate14846.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14837,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14839,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14846,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(11/400),(111/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0741.certificate14829.rectangle,RoutedCases.Batch0741.certificate14830.rectangle,RoutedCases.Batch0741.certificate14831.rectangle,RoutedCases.Batch0741.certificate14832.rectangle,RoutedCases.Batch0741.certificate14833.rectangle,RoutedCases.Batch0741.certificate14834.rectangle,RoutedCases.Batch0741.certificate14836.rectangle,RoutedCases.Batch0741.certificate14838.rectangle,RoutedCases.Batch0742.certificate14840.rectangle,RoutedCases.Batch0742.certificate14842.rectangle,RoutedCases.Batch0742.certificate14843.rectangle,RoutedCases.Batch0742.certificate14847.rectangle,RoutedCases.Batch0742.certificate14849.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14836,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14847,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14849,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(111/4000),(7/250),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0741.certificate14829.rectangle,RoutedCases.Batch0741.certificate14830.rectangle,RoutedCases.Batch0741.certificate14831.rectangle,RoutedCases.Batch0741.certificate14832.rectangle,RoutedCases.Batch0741.certificate14833.rectangle,RoutedCases.Batch0741.certificate14834.rectangle,RoutedCases.Batch0741.certificate14836.rectangle,RoutedCases.Batch0741.certificate14838.rectangle,RoutedCases.Batch0742.certificate14840.rectangle,RoutedCases.Batch0742.certificate14842.rectangle,RoutedCases.Batch0742.certificate14843.rectangle,RoutedCases.Batch0742.certificate14848.rectangle,RoutedCases.Batch0742.certificate14850.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14836,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0741.sound14838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14840,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14848,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0742.sound14850,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(27/1000),(7/250),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source268
