import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0502
import Cycle12.RoutedCases.Batch0503
import Cycle12.RoutedCases.Batch0504

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source186

def strip0 : RatCoverRectangle := ⟨(11/500),(89/4000),2,(some 5)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0502.certificate10054.rectangle,RoutedCases.Batch0502.certificate10056.rectangle,RoutedCases.Batch0502.certificate10058.rectangle,RoutedCases.Batch0503.certificate10060.rectangle,RoutedCases.Batch0503.certificate10062.rectangle,RoutedCases.Batch0503.certificate10064.rectangle,RoutedCases.Batch0503.certificate10066.rectangle,RoutedCases.Batch0503.certificate10068.rectangle,RoutedCases.Batch0503.certificate10071.rectangle,RoutedCases.Batch0503.certificate10072.rectangle,RoutedCases.Batch0503.certificate10075.rectangle,RoutedCases.Batch0503.certificate10076.rectangle,RoutedCases.Batch0504.certificate10081.rectangle,RoutedCases.Batch0504.certificate10082.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10060,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10062,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10064,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10066,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10072,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10081,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10082,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(89/4000),(9/400),2,(some 5)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0502.certificate10054.rectangle,RoutedCases.Batch0502.certificate10056.rectangle,RoutedCases.Batch0502.certificate10058.rectangle,RoutedCases.Batch0503.certificate10060.rectangle,RoutedCases.Batch0503.certificate10062.rectangle,RoutedCases.Batch0503.certificate10064.rectangle,RoutedCases.Batch0503.certificate10066.rectangle,RoutedCases.Batch0503.certificate10068.rectangle,RoutedCases.Batch0503.certificate10071.rectangle,RoutedCases.Batch0503.certificate10072.rectangle,RoutedCases.Batch0503.certificate10075.rectangle,RoutedCases.Batch0503.certificate10076.rectangle,RoutedCases.Batch0504.certificate10081.rectangle,RoutedCases.Batch0504.certificate10083.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10060,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10062,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10064,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10066,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10072,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10081,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10083,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(9/400),(91/4000),2,(some 5)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0502.certificate10055.rectangle,RoutedCases.Batch0502.certificate10057.rectangle,RoutedCases.Batch0502.certificate10059.rectangle,RoutedCases.Batch0503.certificate10061.rectangle,RoutedCases.Batch0503.certificate10063.rectangle,RoutedCases.Batch0503.certificate10065.rectangle,RoutedCases.Batch0503.certificate10067.rectangle,RoutedCases.Batch0503.certificate10069.rectangle,RoutedCases.Batch0503.certificate10070.rectangle,RoutedCases.Batch0503.certificate10073.rectangle,RoutedCases.Batch0503.certificate10074.rectangle,RoutedCases.Batch0503.certificate10077.rectangle,RoutedCases.Batch0503.certificate10079.rectangle,RoutedCases.Batch0504.certificate10084.rectangle,RoutedCases.Batch0504.certificate10086.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10061,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10063,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10065,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10067,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10073,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10074,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10079,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10084,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10086,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(91/4000),(23/1000),2,(some 5)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0502.certificate10055.rectangle,RoutedCases.Batch0502.certificate10057.rectangle,RoutedCases.Batch0502.certificate10059.rectangle,RoutedCases.Batch0503.certificate10061.rectangle,RoutedCases.Batch0503.certificate10063.rectangle,RoutedCases.Batch0503.certificate10065.rectangle,RoutedCases.Batch0503.certificate10067.rectangle,RoutedCases.Batch0503.certificate10069.rectangle,RoutedCases.Batch0503.certificate10070.rectangle,RoutedCases.Batch0503.certificate10073.rectangle,RoutedCases.Batch0503.certificate10074.rectangle,RoutedCases.Batch0503.certificate10078.rectangle,RoutedCases.Batch0504.certificate10080.rectangle,RoutedCases.Batch0504.certificate10085.rectangle,RoutedCases.Batch0504.certificate10087.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0502.sound10059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10061,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10063,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10065,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10067,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10073,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10074,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0503.sound10078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10080,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10085,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0504.sound10087,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(11/500),(23/1000),2,(some 5)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source186
