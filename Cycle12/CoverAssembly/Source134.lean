import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0427
import Cycle12.RoutedCases.Batch0428

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source134

def strip0 : RatCoverRectangle := ⟨(63/1000),(1009/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0427.certificate8542.rectangle,RoutedCases.Batch0427.certificate8544.rectangle,RoutedCases.Batch0427.certificate8546.rectangle,RoutedCases.Batch0427.certificate8548.rectangle,RoutedCases.Batch0427.certificate8549.rectangle,RoutedCases.Batch0427.certificate8550.rectangle,RoutedCases.Batch0427.certificate8551.rectangle,RoutedCases.Batch0427.certificate8552.rectangle,RoutedCases.Batch0427.certificate8553.rectangle,RoutedCases.Batch0427.certificate8554.rectangle,RoutedCases.Batch0427.certificate8555.rectangle,RoutedCases.Batch0427.certificate8556.rectangle,RoutedCases.Batch0427.certificate8557.rectangle,RoutedCases.Batch0427.certificate8558.rectangle,RoutedCases.Batch0427.certificate8559.rectangle,RoutedCases.Batch0428.certificate8560.rectangle,RoutedCases.Batch0428.certificate8561.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8542,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8544,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8546,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8548,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8549,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8551,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8554,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8555,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8556,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8557,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8558,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8559,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8560,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8561,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1009/16000),(101/1600),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0427.certificate8543.rectangle,RoutedCases.Batch0427.certificate8545.rectangle,RoutedCases.Batch0427.certificate8547.rectangle,RoutedCases.Batch0427.certificate8548.rectangle,RoutedCases.Batch0427.certificate8549.rectangle,RoutedCases.Batch0427.certificate8550.rectangle,RoutedCases.Batch0427.certificate8551.rectangle,RoutedCases.Batch0427.certificate8552.rectangle,RoutedCases.Batch0427.certificate8553.rectangle,RoutedCases.Batch0427.certificate8554.rectangle,RoutedCases.Batch0427.certificate8555.rectangle,RoutedCases.Batch0427.certificate8556.rectangle,RoutedCases.Batch0427.certificate8557.rectangle,RoutedCases.Batch0427.certificate8558.rectangle,RoutedCases.Batch0427.certificate8559.rectangle,RoutedCases.Batch0428.certificate8560.rectangle,RoutedCases.Batch0428.certificate8561.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8543,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8545,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8547,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8548,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8549,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8551,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8554,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8555,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8556,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8557,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8558,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0427.sound8559,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8560,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0428.sound8561,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(63/1000),(101/1600),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source134
