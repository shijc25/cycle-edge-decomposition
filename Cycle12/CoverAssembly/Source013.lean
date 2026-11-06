import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0021
import Cycle12.RoutedCases.Batch0022
import Cycle12.RoutedCases.Batch0023
import Cycle12.RoutedCases.Batch0024

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source013

def strip0 : RatCoverRectangle := ⟨(7/500),(57/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0021.certificate430.rectangle,RoutedCases.Batch0021.certificate432.rectangle,RoutedCases.Batch0022.certificate441.rectangle,RoutedCases.Batch0022.certificate443.rectangle,RoutedCases.Batch0022.certificate450.rectangle,RoutedCases.Batch0022.certificate452.rectangle,RoutedCases.Batch0023.certificate462.rectangle,RoutedCases.Batch0023.certificate464.rectangle,RoutedCases.Batch0023.certificate473.rectangle,RoutedCases.Batch0023.certificate475.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound430,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound432,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound441,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound443,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound450,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound452,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound462,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound464,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound473,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound475,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(57/4000),(29/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0021.certificate431.rectangle,RoutedCases.Batch0021.certificate433.rectangle,RoutedCases.Batch0022.certificate442.rectangle,RoutedCases.Batch0022.certificate444.rectangle,RoutedCases.Batch0022.certificate451.rectangle,RoutedCases.Batch0022.certificate453.rectangle,RoutedCases.Batch0023.certificate463.rectangle,RoutedCases.Batch0023.certificate465.rectangle,RoutedCases.Batch0023.certificate474.rectangle,RoutedCases.Batch0023.certificate476.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound431,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound433,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound442,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound444,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound451,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound453,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound463,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound465,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound474,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound476,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(29/2000),(59/4000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0021.certificate434.rectangle,RoutedCases.Batch0021.certificate435.rectangle,RoutedCases.Batch0021.certificate438.rectangle,RoutedCases.Batch0022.certificate445.rectangle,RoutedCases.Batch0022.certificate448.rectangle,RoutedCases.Batch0022.certificate454.rectangle,RoutedCases.Batch0022.certificate455.rectangle,RoutedCases.Batch0022.certificate458.rectangle,RoutedCases.Batch0022.certificate459.rectangle,RoutedCases.Batch0023.certificate466.rectangle,RoutedCases.Batch0023.certificate467.rectangle,RoutedCases.Batch0023.certificate470.rectangle,RoutedCases.Batch0023.certificate477.rectangle,RoutedCases.Batch0024.certificate480.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound434,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound438,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound445,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound448,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound454,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound455,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound466,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound467,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound470,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound477,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0024.sound480,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(59/4000),(3/200),1,(some 2)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0021.certificate436.rectangle,RoutedCases.Batch0021.certificate437.rectangle,RoutedCases.Batch0021.certificate439.rectangle,RoutedCases.Batch0022.certificate440.rectangle,RoutedCases.Batch0022.certificate446.rectangle,RoutedCases.Batch0022.certificate447.rectangle,RoutedCases.Batch0022.certificate449.rectangle,RoutedCases.Batch0022.certificate456.rectangle,RoutedCases.Batch0022.certificate457.rectangle,RoutedCases.Batch0023.certificate460.rectangle,RoutedCases.Batch0023.certificate461.rectangle,RoutedCases.Batch0023.certificate468.rectangle,RoutedCases.Batch0023.certificate469.rectangle,RoutedCases.Batch0023.certificate471.rectangle,RoutedCases.Batch0023.certificate472.rectangle,RoutedCases.Batch0023.certificate478.rectangle,RoutedCases.Batch0023.certificate479.rectangle,RoutedCases.Batch0024.certificate481.rectangle,RoutedCases.Batch0024.certificate482.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound437,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0021.sound439,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound440,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound446,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound447,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound449,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound456,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0022.sound457,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound468,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound469,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound471,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound472,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound478,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0023.sound479,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0024.sound481,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0024.sound482,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/500),(3/200),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source013
