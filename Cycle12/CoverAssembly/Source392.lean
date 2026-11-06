import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0893
import Cycle12.RoutedCases.Batch0894
import Cycle12.RoutedCases.Batch0895

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source392

def strip0 : RatCoverRectangle := ⟨(11/200),(441/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17875.rectangle,RoutedCases.Batch0893.certificate17876.rectangle,RoutedCases.Batch0893.certificate17877.rectangle,RoutedCases.Batch0893.certificate17878.rectangle,RoutedCases.Batch0893.certificate17879.rectangle,RoutedCases.Batch0894.certificate17880.rectangle,RoutedCases.Batch0894.certificate17882.rectangle,RoutedCases.Batch0894.certificate17884.rectangle,RoutedCases.Batch0894.certificate17886.rectangle,RoutedCases.Batch0894.certificate17888.rectangle,RoutedCases.Batch0894.certificate17891.rectangle,RoutedCases.Batch0894.certificate17892.rectangle,RoutedCases.Batch0894.certificate17895.rectangle,RoutedCases.Batch0894.certificate17897.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17878,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17880,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17891,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17892,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17895,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17897,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(441/8000),(221/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17875.rectangle,RoutedCases.Batch0893.certificate17876.rectangle,RoutedCases.Batch0893.certificate17877.rectangle,RoutedCases.Batch0893.certificate17878.rectangle,RoutedCases.Batch0893.certificate17879.rectangle,RoutedCases.Batch0894.certificate17880.rectangle,RoutedCases.Batch0894.certificate17882.rectangle,RoutedCases.Batch0894.certificate17884.rectangle,RoutedCases.Batch0894.certificate17886.rectangle,RoutedCases.Batch0894.certificate17888.rectangle,RoutedCases.Batch0894.certificate17891.rectangle,RoutedCases.Batch0894.certificate17893.rectangle,RoutedCases.Batch0894.certificate17896.rectangle,RoutedCases.Batch0894.certificate17898.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17878,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17880,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17891,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17893,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17896,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17898,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(221/4000),(111/2000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17875.rectangle,RoutedCases.Batch0893.certificate17876.rectangle,RoutedCases.Batch0893.certificate17877.rectangle,RoutedCases.Batch0893.certificate17878.rectangle,RoutedCases.Batch0893.certificate17879.rectangle,RoutedCases.Batch0894.certificate17880.rectangle,RoutedCases.Batch0894.certificate17882.rectangle,RoutedCases.Batch0894.certificate17884.rectangle,RoutedCases.Batch0894.certificate17886.rectangle,RoutedCases.Batch0894.certificate17889.rectangle,RoutedCases.Batch0894.certificate17894.rectangle,RoutedCases.Batch0894.certificate17899.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17878,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17880,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17889,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17894,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17899,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(111/2000),(223/4000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17875.rectangle,RoutedCases.Batch0893.certificate17876.rectangle,RoutedCases.Batch0893.certificate17877.rectangle,RoutedCases.Batch0893.certificate17878.rectangle,RoutedCases.Batch0893.certificate17879.rectangle,RoutedCases.Batch0894.certificate17881.rectangle,RoutedCases.Batch0894.certificate17883.rectangle,RoutedCases.Batch0894.certificate17885.rectangle,RoutedCases.Batch0894.certificate17887.rectangle,RoutedCases.Batch0894.certificate17890.rectangle,RoutedCases.Batch0895.certificate17900.rectangle,RoutedCases.Batch0895.certificate17902.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17878,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17883,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0895.sound17900,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0895.sound17902,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(223/4000),(7/125),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17875.rectangle,RoutedCases.Batch0893.certificate17876.rectangle,RoutedCases.Batch0893.certificate17877.rectangle,RoutedCases.Batch0893.certificate17878.rectangle,RoutedCases.Batch0893.certificate17879.rectangle,RoutedCases.Batch0894.certificate17881.rectangle,RoutedCases.Batch0894.certificate17883.rectangle,RoutedCases.Batch0894.certificate17885.rectangle,RoutedCases.Batch0894.certificate17887.rectangle,RoutedCases.Batch0894.certificate17890.rectangle,RoutedCases.Batch0895.certificate17901.rectangle,RoutedCases.Batch0895.certificate17903.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17875,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17876,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17877,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17878,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17879,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17883,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0894.sound17890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0895.sound17901,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0895.sound17903,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/200),(7/125),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source392
