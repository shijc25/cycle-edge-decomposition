import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0831
import Cycle12.RoutedCases.Batch0832
import Cycle12.RoutedCases.Batch0833

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source340

def strip0 : RatCoverRectangle := ⟨(11/1000),(9/800),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16635.rectangle,RoutedCases.Batch0831.certificate16636.rectangle,RoutedCases.Batch0831.certificate16637.rectangle,RoutedCases.Batch0831.certificate16639.rectangle,RoutedCases.Batch0832.certificate16641.rectangle,RoutedCases.Batch0832.certificate16646.rectangle,RoutedCases.Batch0832.certificate16647.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16647,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(9/800),(23/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16635.rectangle,RoutedCases.Batch0831.certificate16636.rectangle,RoutedCases.Batch0831.certificate16637.rectangle,RoutedCases.Batch0831.certificate16639.rectangle,RoutedCases.Batch0832.certificate16641.rectangle,RoutedCases.Batch0832.certificate16646.rectangle,RoutedCases.Batch0832.certificate16648.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16648,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(23/2000),(47/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16635.rectangle,RoutedCases.Batch0831.certificate16636.rectangle,RoutedCases.Batch0831.certificate16638.rectangle,RoutedCases.Batch0832.certificate16640.rectangle,RoutedCases.Batch0832.certificate16642.rectangle,RoutedCases.Batch0832.certificate16644.rectangle,RoutedCases.Batch0832.certificate16649.rectangle,RoutedCases.Batch0832.certificate16653.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16649,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16653,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(47/4000),(19/1600),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16635.rectangle,RoutedCases.Batch0831.certificate16636.rectangle,RoutedCases.Batch0831.certificate16638.rectangle,RoutedCases.Batch0832.certificate16640.rectangle,RoutedCases.Batch0832.certificate16643.rectangle,RoutedCases.Batch0832.certificate16645.rectangle,RoutedCases.Batch0832.certificate16650.rectangle,RoutedCases.Batch0832.certificate16651.rectangle,RoutedCases.Batch0832.certificate16654.rectangle,RoutedCases.Batch0832.certificate16656.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16651,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16654,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16656,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(19/1600),(381/32000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16635.rectangle,RoutedCases.Batch0831.certificate16636.rectangle,RoutedCases.Batch0831.certificate16638.rectangle,RoutedCases.Batch0832.certificate16640.rectangle,RoutedCases.Batch0832.certificate16643.rectangle,RoutedCases.Batch0832.certificate16645.rectangle,RoutedCases.Batch0832.certificate16650.rectangle,RoutedCases.Batch0832.certificate16652.rectangle,RoutedCases.Batch0832.certificate16655.rectangle,RoutedCases.Batch0832.certificate16657.rectangle,RoutedCases.Batch0832.certificate16659.rectangle,RoutedCases.Batch0833.certificate16660.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16652,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16655,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16657,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16659,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16660,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(381/32000),(191/16000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16635.rectangle,RoutedCases.Batch0831.certificate16636.rectangle,RoutedCases.Batch0831.certificate16638.rectangle,RoutedCases.Batch0832.certificate16640.rectangle,RoutedCases.Batch0832.certificate16643.rectangle,RoutedCases.Batch0832.certificate16645.rectangle,RoutedCases.Batch0832.certificate16650.rectangle,RoutedCases.Batch0832.certificate16652.rectangle,RoutedCases.Batch0832.certificate16655.rectangle,RoutedCases.Batch0832.certificate16657.rectangle,RoutedCases.Batch0832.certificate16659.rectangle,RoutedCases.Batch0833.certificate16661.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16652,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16655,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16657,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16659,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16661,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip6 : RatCoverRectangle := ⟨(191/16000),(3/250),20,(some 100)⟩
def pieces6 : List RatCoverRectangle := [RoutedCases.Batch0831.certificate16635.rectangle,RoutedCases.Batch0831.certificate16636.rectangle,RoutedCases.Batch0831.certificate16638.rectangle,RoutedCases.Batch0832.certificate16640.rectangle,RoutedCases.Batch0832.certificate16643.rectangle,RoutedCases.Batch0832.certificate16645.rectangle,RoutedCases.Batch0832.certificate16650.rectangle,RoutedCases.Batch0832.certificate16652.rectangle,RoutedCases.Batch0832.certificate16655.rectangle,RoutedCases.Batch0832.certificate16658.rectangle,RoutedCases.Batch0833.certificate16662.rectangle]
theorem valid6 : strip6.JoinS pieces6 := by decide +kernel
theorem sound6 : strip6.Sound := rat_cover_join_s_sound strip6 pieces6 valid6 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0831.sound16638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16652,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16655,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0832.sound16658,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16662,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/1000),(3/250),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5,strip6]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source340
