import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0726
import Cycle12.RoutedCases.Batch0727

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source258

def strip0 : RatCoverRectangle := ⟨(17/1000),(69/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0726.certificate14531.rectangle,RoutedCases.Batch0726.certificate14532.rectangle,RoutedCases.Batch0726.certificate14533.rectangle,RoutedCases.Batch0726.certificate14534.rectangle,RoutedCases.Batch0726.certificate14535.rectangle,RoutedCases.Batch0726.certificate14537.rectangle,RoutedCases.Batch0726.certificate14539.rectangle,RoutedCases.Batch0727.certificate14542.rectangle,RoutedCases.Batch0727.certificate14543.rectangle,RoutedCases.Batch0727.certificate14548.rectangle,RoutedCases.Batch0727.certificate14550.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14531,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14532,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14533,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14534,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14535,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14537,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14539,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14542,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14543,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14548,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14550,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(69/4000),(7/400),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0726.certificate14531.rectangle,RoutedCases.Batch0726.certificate14532.rectangle,RoutedCases.Batch0726.certificate14533.rectangle,RoutedCases.Batch0726.certificate14534.rectangle,RoutedCases.Batch0726.certificate14535.rectangle,RoutedCases.Batch0726.certificate14537.rectangle,RoutedCases.Batch0726.certificate14539.rectangle,RoutedCases.Batch0727.certificate14542.rectangle,RoutedCases.Batch0727.certificate14543.rectangle,RoutedCases.Batch0727.certificate14549.rectangle,RoutedCases.Batch0727.certificate14551.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14531,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14532,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14533,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14534,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14535,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14537,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14539,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14542,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14543,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14549,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14551,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(7/400),(71/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0726.certificate14531.rectangle,RoutedCases.Batch0726.certificate14532.rectangle,RoutedCases.Batch0726.certificate14533.rectangle,RoutedCases.Batch0726.certificate14534.rectangle,RoutedCases.Batch0726.certificate14536.rectangle,RoutedCases.Batch0726.certificate14538.rectangle,RoutedCases.Batch0727.certificate14540.rectangle,RoutedCases.Batch0727.certificate14541.rectangle,RoutedCases.Batch0727.certificate14544.rectangle,RoutedCases.Batch0727.certificate14546.rectangle,RoutedCases.Batch0727.certificate14552.rectangle,RoutedCases.Batch0727.certificate14554.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14531,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14532,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14533,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14534,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14536,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14538,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14540,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14541,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14544,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14546,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14554,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(71/4000),(143/8000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0726.certificate14531.rectangle,RoutedCases.Batch0726.certificate14532.rectangle,RoutedCases.Batch0726.certificate14533.rectangle,RoutedCases.Batch0726.certificate14534.rectangle,RoutedCases.Batch0726.certificate14536.rectangle,RoutedCases.Batch0726.certificate14538.rectangle,RoutedCases.Batch0727.certificate14540.rectangle,RoutedCases.Batch0727.certificate14541.rectangle,RoutedCases.Batch0727.certificate14545.rectangle,RoutedCases.Batch0727.certificate14547.rectangle,RoutedCases.Batch0727.certificate14553.rectangle,RoutedCases.Batch0727.certificate14555.rectangle,RoutedCases.Batch0727.certificate14557.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14531,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14532,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14533,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14534,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14536,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14538,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14540,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14541,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14545,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14547,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14555,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14557,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(143/8000),(9/500),5,(some 20)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0726.certificate14531.rectangle,RoutedCases.Batch0726.certificate14532.rectangle,RoutedCases.Batch0726.certificate14533.rectangle,RoutedCases.Batch0726.certificate14534.rectangle,RoutedCases.Batch0726.certificate14536.rectangle,RoutedCases.Batch0726.certificate14538.rectangle,RoutedCases.Batch0727.certificate14540.rectangle,RoutedCases.Batch0727.certificate14541.rectangle,RoutedCases.Batch0727.certificate14545.rectangle,RoutedCases.Batch0727.certificate14547.rectangle,RoutedCases.Batch0727.certificate14553.rectangle,RoutedCases.Batch0727.certificate14556.rectangle,RoutedCases.Batch0727.certificate14558.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14531,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14532,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14533,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14534,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14536,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0726.sound14538,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14540,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14541,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14545,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14547,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14556,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0727.sound14558,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(17/1000),(9/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source258
