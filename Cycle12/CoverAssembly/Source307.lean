import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0797

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source307

def strip0 : RatCoverRectangle := ⟨(59/1000),(473/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0797.certificate15941.rectangle,RoutedCases.Batch0797.certificate15942.rectangle,RoutedCases.Batch0797.certificate15943.rectangle,RoutedCases.Batch0797.certificate15944.rectangle,RoutedCases.Batch0797.certificate15945.rectangle,RoutedCases.Batch0797.certificate15946.rectangle,RoutedCases.Batch0797.certificate15947.rectangle,RoutedCases.Batch0797.certificate15948.rectangle,RoutedCases.Batch0797.certificate15949.rectangle,RoutedCases.Batch0797.certificate15950.rectangle,RoutedCases.Batch0797.certificate15952.rectangle,RoutedCases.Batch0797.certificate15954.rectangle,RoutedCases.Batch0797.certificate15956.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15952,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15954,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15956,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(473/8000),(237/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0797.certificate15941.rectangle,RoutedCases.Batch0797.certificate15942.rectangle,RoutedCases.Batch0797.certificate15943.rectangle,RoutedCases.Batch0797.certificate15944.rectangle,RoutedCases.Batch0797.certificate15945.rectangle,RoutedCases.Batch0797.certificate15946.rectangle,RoutedCases.Batch0797.certificate15947.rectangle,RoutedCases.Batch0797.certificate15948.rectangle,RoutedCases.Batch0797.certificate15949.rectangle,RoutedCases.Batch0797.certificate15950.rectangle,RoutedCases.Batch0797.certificate15952.rectangle,RoutedCases.Batch0797.certificate15955.rectangle,RoutedCases.Batch0797.certificate15956.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15952,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15955,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15956,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(237/4000),(119/2000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0797.certificate15941.rectangle,RoutedCases.Batch0797.certificate15942.rectangle,RoutedCases.Batch0797.certificate15943.rectangle,RoutedCases.Batch0797.certificate15944.rectangle,RoutedCases.Batch0797.certificate15945.rectangle,RoutedCases.Batch0797.certificate15946.rectangle,RoutedCases.Batch0797.certificate15947.rectangle,RoutedCases.Batch0797.certificate15948.rectangle,RoutedCases.Batch0797.certificate15949.rectangle,RoutedCases.Batch0797.certificate15951.rectangle,RoutedCases.Batch0797.certificate15953.rectangle,RoutedCases.Batch0797.certificate15957.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15941,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15951,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15953,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15957,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(59/1000),(119/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source307
