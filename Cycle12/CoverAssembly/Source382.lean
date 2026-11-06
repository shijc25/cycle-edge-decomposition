import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0881
import Cycle12.RoutedCases.Batch0882

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source382

def strip0 : RatCoverRectangle := ⟨(47/1000),(377/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17633.rectangle,RoutedCases.Batch0881.certificate17635.rectangle,RoutedCases.Batch0881.certificate17637.rectangle,RoutedCases.Batch0881.certificate17638.rectangle,RoutedCases.Batch0882.certificate17643.rectangle,RoutedCases.Batch0882.certificate17645.rectangle,RoutedCases.Batch0882.certificate17646.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17646,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(377/8000),(189/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17633.rectangle,RoutedCases.Batch0881.certificate17635.rectangle,RoutedCases.Batch0881.certificate17637.rectangle,RoutedCases.Batch0881.certificate17638.rectangle,RoutedCases.Batch0882.certificate17643.rectangle,RoutedCases.Batch0882.certificate17645.rectangle,RoutedCases.Batch0882.certificate17647.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17647,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(189/4000),(379/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17633.rectangle,RoutedCases.Batch0881.certificate17635.rectangle,RoutedCases.Batch0881.certificate17637.rectangle,RoutedCases.Batch0881.certificate17639.rectangle,RoutedCases.Batch0882.certificate17644.rectangle,RoutedCases.Batch0882.certificate17648.rectangle,RoutedCases.Batch0882.certificate17649.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17648,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17649,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(379/8000),(19/400),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17633.rectangle,RoutedCases.Batch0881.certificate17635.rectangle,RoutedCases.Batch0881.certificate17637.rectangle,RoutedCases.Batch0881.certificate17639.rectangle,RoutedCases.Batch0882.certificate17644.rectangle,RoutedCases.Batch0882.certificate17648.rectangle,RoutedCases.Batch0882.certificate17650.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17633,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17635,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17648,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17650,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(19/400),(381/8000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17634.rectangle,RoutedCases.Batch0881.certificate17636.rectangle,RoutedCases.Batch0882.certificate17640.rectangle,RoutedCases.Batch0882.certificate17641.rectangle,RoutedCases.Batch0882.certificate17651.rectangle,RoutedCases.Batch0882.certificate17653.rectangle,RoutedCases.Batch0882.certificate17654.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17651,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17653,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17654,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(381/8000),(191/4000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17634.rectangle,RoutedCases.Batch0881.certificate17636.rectangle,RoutedCases.Batch0882.certificate17640.rectangle,RoutedCases.Batch0882.certificate17641.rectangle,RoutedCases.Batch0882.certificate17651.rectangle,RoutedCases.Batch0882.certificate17653.rectangle,RoutedCases.Batch0882.certificate17655.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17651,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17653,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17655,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip6 : RatCoverRectangle := ⟨(191/4000),(383/8000),20,(some 100)⟩
def pieces6 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17634.rectangle,RoutedCases.Batch0881.certificate17636.rectangle,RoutedCases.Batch0882.certificate17640.rectangle,RoutedCases.Batch0882.certificate17642.rectangle,RoutedCases.Batch0882.certificate17652.rectangle,RoutedCases.Batch0882.certificate17656.rectangle,RoutedCases.Batch0882.certificate17657.rectangle]
theorem valid6 : strip6.JoinS pieces6 := by decide +kernel
theorem sound6 : strip6.Sound := rat_cover_join_s_sound strip6 pieces6 valid6 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17652,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17656,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17657,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip7 : RatCoverRectangle := ⟨(383/8000),(6/125),20,(some 100)⟩
def pieces7 : List RatCoverRectangle := [RoutedCases.Batch0881.certificate17629.rectangle,RoutedCases.Batch0881.certificate17630.rectangle,RoutedCases.Batch0881.certificate17631.rectangle,RoutedCases.Batch0881.certificate17632.rectangle,RoutedCases.Batch0881.certificate17634.rectangle,RoutedCases.Batch0881.certificate17636.rectangle,RoutedCases.Batch0882.certificate17640.rectangle,RoutedCases.Batch0882.certificate17642.rectangle,RoutedCases.Batch0882.certificate17652.rectangle,RoutedCases.Batch0882.certificate17656.rectangle,RoutedCases.Batch0882.certificate17658.rectangle]
theorem valid7 : strip7.JoinS pieces7 := by decide +kernel
theorem sound7 : strip7.Sound := rat_cover_join_s_sound strip7 pieces7 valid7 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17629,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17630,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17631,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17632,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17634,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0881.sound17636,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17652,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17656,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0882.sound17658,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(47/1000),(6/125),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5,strip6,strip7]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_cons.mpr ⟨sound7,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source382
