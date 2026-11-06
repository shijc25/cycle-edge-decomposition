import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0848
import Cycle12.RoutedCases.Batch0849

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source361

def strip0 : RatCoverRectangle := ⟨(13/500),(21/800),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0848.certificate16964.rectangle,RoutedCases.Batch0848.certificate16965.rectangle,RoutedCases.Batch0848.certificate16966.rectangle,RoutedCases.Batch0848.certificate16967.rectangle,RoutedCases.Batch0848.certificate16968.rectangle,RoutedCases.Batch0848.certificate16970.rectangle,RoutedCases.Batch0848.certificate16972.rectangle,RoutedCases.Batch0848.certificate16974.rectangle,RoutedCases.Batch0848.certificate16976.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16968,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16970,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16972,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16974,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16976,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(21/800),(53/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0848.certificate16964.rectangle,RoutedCases.Batch0848.certificate16965.rectangle,RoutedCases.Batch0848.certificate16966.rectangle,RoutedCases.Batch0848.certificate16967.rectangle,RoutedCases.Batch0848.certificate16968.rectangle,RoutedCases.Batch0848.certificate16970.rectangle,RoutedCases.Batch0848.certificate16972.rectangle,RoutedCases.Batch0848.certificate16975.rectangle,RoutedCases.Batch0848.certificate16977.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16968,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16970,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16972,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16975,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16977,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(53/2000),(107/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0848.certificate16964.rectangle,RoutedCases.Batch0848.certificate16965.rectangle,RoutedCases.Batch0848.certificate16966.rectangle,RoutedCases.Batch0848.certificate16967.rectangle,RoutedCases.Batch0848.certificate16969.rectangle,RoutedCases.Batch0848.certificate16971.rectangle,RoutedCases.Batch0848.certificate16973.rectangle,RoutedCases.Batch0848.certificate16978.rectangle,RoutedCases.Batch0849.certificate16980.rectangle,RoutedCases.Batch0849.certificate16981.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16971,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16978,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16980,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16981,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(107/4000),(43/1600),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0848.certificate16964.rectangle,RoutedCases.Batch0848.certificate16965.rectangle,RoutedCases.Batch0848.certificate16966.rectangle,RoutedCases.Batch0848.certificate16967.rectangle,RoutedCases.Batch0848.certificate16969.rectangle,RoutedCases.Batch0848.certificate16971.rectangle,RoutedCases.Batch0848.certificate16973.rectangle,RoutedCases.Batch0848.certificate16979.rectangle,RoutedCases.Batch0849.certificate16982.rectangle,RoutedCases.Batch0849.certificate16984.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16971,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16979,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16982,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16984,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(43/1600),(431/16000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0848.certificate16964.rectangle,RoutedCases.Batch0848.certificate16965.rectangle,RoutedCases.Batch0848.certificate16966.rectangle,RoutedCases.Batch0848.certificate16967.rectangle,RoutedCases.Batch0848.certificate16969.rectangle,RoutedCases.Batch0848.certificate16971.rectangle,RoutedCases.Batch0848.certificate16973.rectangle,RoutedCases.Batch0848.certificate16979.rectangle,RoutedCases.Batch0849.certificate16983.rectangle,RoutedCases.Batch0849.certificate16985.rectangle,RoutedCases.Batch0849.certificate16986.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16971,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16979,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16983,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16985,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16986,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(431/16000),(27/1000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0848.certificate16964.rectangle,RoutedCases.Batch0848.certificate16965.rectangle,RoutedCases.Batch0848.certificate16966.rectangle,RoutedCases.Batch0848.certificate16967.rectangle,RoutedCases.Batch0848.certificate16969.rectangle,RoutedCases.Batch0848.certificate16971.rectangle,RoutedCases.Batch0848.certificate16973.rectangle,RoutedCases.Batch0848.certificate16979.rectangle,RoutedCases.Batch0849.certificate16983.rectangle,RoutedCases.Batch0849.certificate16985.rectangle,RoutedCases.Batch0849.certificate16987.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16971,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0848.sound16979,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16983,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16985,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0849.sound16987,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/500),(27/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source361
