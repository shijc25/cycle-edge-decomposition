import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0032
import Cycle12.RoutedCases.Batch0033
import Cycle12.RoutedCases.Batch0034
import Cycle12.RoutedCases.Batch0035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source017

def strip0 : RatCoverRectangle := ⟨(9/500),(73/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0032.certificate656.rectangle,RoutedCases.Batch0032.certificate658.rectangle,RoutedCases.Batch0033.certificate667.rectangle,RoutedCases.Batch0033.certificate669.rectangle,RoutedCases.Batch0033.certificate675.rectangle,RoutedCases.Batch0033.certificate677.rectangle,RoutedCases.Batch0034.certificate683.rectangle,RoutedCases.Batch0034.certificate685.rectangle,RoutedCases.Batch0034.certificate691.rectangle,RoutedCases.Batch0034.certificate693.rectangle,RoutedCases.Batch0034.certificate699.rectangle,RoutedCases.Batch0035.certificate704.rectangle,RoutedCases.Batch0035.certificate706.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound656,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound658,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound667,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound669,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound675,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound677,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound683,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound685,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound691,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound693,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound699,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound704,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound706,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(73/4000),(37/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0032.certificate657.rectangle,RoutedCases.Batch0032.certificate659.rectangle,RoutedCases.Batch0033.certificate668.rectangle,RoutedCases.Batch0033.certificate670.rectangle,RoutedCases.Batch0033.certificate676.rectangle,RoutedCases.Batch0033.certificate678.rectangle,RoutedCases.Batch0034.certificate684.rectangle,RoutedCases.Batch0034.certificate686.rectangle,RoutedCases.Batch0034.certificate692.rectangle,RoutedCases.Batch0034.certificate694.rectangle,RoutedCases.Batch0035.certificate700.rectangle,RoutedCases.Batch0035.certificate705.rectangle,RoutedCases.Batch0035.certificate707.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound657,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0032.sound659,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound668,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound670,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound676,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound678,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound692,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound694,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound700,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound705,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound707,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(37/2000),(3/160),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0033.certificate660.rectangle,RoutedCases.Batch0033.certificate661.rectangle,RoutedCases.Batch0033.certificate664.rectangle,RoutedCases.Batch0033.certificate671.rectangle,RoutedCases.Batch0033.certificate673.rectangle,RoutedCases.Batch0033.certificate679.rectangle,RoutedCases.Batch0034.certificate681.rectangle,RoutedCases.Batch0034.certificate687.rectangle,RoutedCases.Batch0034.certificate689.rectangle,RoutedCases.Batch0034.certificate695.rectangle,RoutedCases.Batch0034.certificate697.rectangle,RoutedCases.Batch0035.certificate701.rectangle,RoutedCases.Batch0035.certificate708.rectangle,RoutedCases.Batch0035.certificate711.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound660,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound661,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound664,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound671,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound673,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound679,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound687,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound689,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound695,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound697,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound701,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound708,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound711,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(3/160),(19/1000),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0033.certificate662.rectangle,RoutedCases.Batch0033.certificate663.rectangle,RoutedCases.Batch0033.certificate665.rectangle,RoutedCases.Batch0033.certificate666.rectangle,RoutedCases.Batch0033.certificate672.rectangle,RoutedCases.Batch0033.certificate674.rectangle,RoutedCases.Batch0034.certificate680.rectangle,RoutedCases.Batch0034.certificate682.rectangle,RoutedCases.Batch0034.certificate688.rectangle,RoutedCases.Batch0034.certificate690.rectangle,RoutedCases.Batch0034.certificate696.rectangle,RoutedCases.Batch0034.certificate698.rectangle,RoutedCases.Batch0035.certificate702.rectangle,RoutedCases.Batch0035.certificate703.rectangle,RoutedCases.Batch0035.certificate709.rectangle,RoutedCases.Batch0035.certificate710.rectangle,RoutedCases.Batch0035.certificate712.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound662,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound663,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound665,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound666,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound672,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0033.sound674,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound680,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound690,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound696,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0034.sound698,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound702,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound703,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound710,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0035.sound712,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/500),(19/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source017
