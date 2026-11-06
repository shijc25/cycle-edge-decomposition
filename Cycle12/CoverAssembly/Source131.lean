import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0422
import Cycle12.RoutedCases.Batch0423

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source131

def strip0 : RatCoverRectangle := ⟨(1/16),(1001/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0422.certificate8449.rectangle,RoutedCases.Batch0422.certificate8450.rectangle,RoutedCases.Batch0422.certificate8452.rectangle,RoutedCases.Batch0422.certificate8454.rectangle,RoutedCases.Batch0422.certificate8456.rectangle,RoutedCases.Batch0422.certificate8458.rectangle,RoutedCases.Batch0422.certificate8459.rectangle,RoutedCases.Batch0423.certificate8460.rectangle,RoutedCases.Batch0423.certificate8461.rectangle,RoutedCases.Batch0423.certificate8462.rectangle,RoutedCases.Batch0423.certificate8463.rectangle,RoutedCases.Batch0423.certificate8464.rectangle,RoutedCases.Batch0423.certificate8465.rectangle,RoutedCases.Batch0423.certificate8466.rectangle,RoutedCases.Batch0423.certificate8467.rectangle,RoutedCases.Batch0423.certificate8468.rectangle,RoutedCases.Batch0423.certificate8469.rectangle,RoutedCases.Batch0423.certificate8470.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8449,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8450,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8452,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8454,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8456,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8462,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8463,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8464,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8465,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8466,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8467,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8468,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8469,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8470,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1001/16000),(501/8000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0422.certificate8451.rectangle,RoutedCases.Batch0422.certificate8453.rectangle,RoutedCases.Batch0422.certificate8455.rectangle,RoutedCases.Batch0422.certificate8457.rectangle,RoutedCases.Batch0422.certificate8458.rectangle,RoutedCases.Batch0422.certificate8459.rectangle,RoutedCases.Batch0423.certificate8460.rectangle,RoutedCases.Batch0423.certificate8461.rectangle,RoutedCases.Batch0423.certificate8462.rectangle,RoutedCases.Batch0423.certificate8463.rectangle,RoutedCases.Batch0423.certificate8464.rectangle,RoutedCases.Batch0423.certificate8465.rectangle,RoutedCases.Batch0423.certificate8466.rectangle,RoutedCases.Batch0423.certificate8467.rectangle,RoutedCases.Batch0423.certificate8468.rectangle,RoutedCases.Batch0423.certificate8469.rectangle,RoutedCases.Batch0423.certificate8470.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8451,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8453,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8455,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8457,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8458,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0422.sound8459,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8460,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8461,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8462,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8463,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8464,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8465,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8466,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8467,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8468,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8469,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0423.sound8470,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/16),(501/8000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source131
