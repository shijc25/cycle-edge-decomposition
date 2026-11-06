import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0309
import Cycle12.RoutedCases.Batch0310

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source079

def strip0 : RatCoverRectangle := ⟨(1/20),(401/8000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0309.certificate6197.rectangle,RoutedCases.Batch0309.certificate6199.rectangle,RoutedCases.Batch0310.certificate6200.rectangle,RoutedCases.Batch0310.certificate6201.rectangle,RoutedCases.Batch0310.certificate6202.rectangle,RoutedCases.Batch0310.certificate6203.rectangle,RoutedCases.Batch0310.certificate6204.rectangle,RoutedCases.Batch0310.certificate6205.rectangle,RoutedCases.Batch0310.certificate6206.rectangle,RoutedCases.Batch0310.certificate6207.rectangle,RoutedCases.Batch0310.certificate6208.rectangle,RoutedCases.Batch0310.certificate6209.rectangle,RoutedCases.Batch0310.certificate6210.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0309.sound6197,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0309.sound6199,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6200,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6201,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6202,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6203,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6204,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6205,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6206,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6208,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6210,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(401/8000),(201/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0309.certificate6198.rectangle,RoutedCases.Batch0309.certificate6199.rectangle,RoutedCases.Batch0310.certificate6200.rectangle,RoutedCases.Batch0310.certificate6201.rectangle,RoutedCases.Batch0310.certificate6202.rectangle,RoutedCases.Batch0310.certificate6203.rectangle,RoutedCases.Batch0310.certificate6204.rectangle,RoutedCases.Batch0310.certificate6205.rectangle,RoutedCases.Batch0310.certificate6206.rectangle,RoutedCases.Batch0310.certificate6207.rectangle,RoutedCases.Batch0310.certificate6208.rectangle,RoutedCases.Batch0310.certificate6209.rectangle,RoutedCases.Batch0310.certificate6210.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0309.sound6198,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0309.sound6199,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6200,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6201,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6202,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6203,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6204,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6205,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6206,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6208,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6210,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/20),(201/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source079
