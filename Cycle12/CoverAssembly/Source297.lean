import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0785
import Cycle12.RoutedCases.Batch0786

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source297

def strip0 : RatCoverRectangle := ⟨(53/1000),(17/320),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0785.certificate15708.rectangle,RoutedCases.Batch0785.certificate15709.rectangle,RoutedCases.Batch0785.certificate15710.rectangle,RoutedCases.Batch0785.certificate15711.rectangle,RoutedCases.Batch0785.certificate15712.rectangle,RoutedCases.Batch0785.certificate15713.rectangle,RoutedCases.Batch0785.certificate15714.rectangle,RoutedCases.Batch0785.certificate15715.rectangle,RoutedCases.Batch0785.certificate15717.rectangle,RoutedCases.Batch0785.certificate15719.rectangle,RoutedCases.Batch0786.certificate15721.rectangle,RoutedCases.Batch0786.certificate15723.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15708,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15710,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15711,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15717,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15719,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15721,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15723,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(17/320),(213/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0785.certificate15708.rectangle,RoutedCases.Batch0785.certificate15709.rectangle,RoutedCases.Batch0785.certificate15710.rectangle,RoutedCases.Batch0785.certificate15711.rectangle,RoutedCases.Batch0785.certificate15712.rectangle,RoutedCases.Batch0785.certificate15713.rectangle,RoutedCases.Batch0785.certificate15714.rectangle,RoutedCases.Batch0785.certificate15715.rectangle,RoutedCases.Batch0785.certificate15717.rectangle,RoutedCases.Batch0785.certificate15719.rectangle,RoutedCases.Batch0786.certificate15722.rectangle,RoutedCases.Batch0786.certificate15724.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15708,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15710,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15711,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15715,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15717,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15719,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15722,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15724,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(213/4000),(107/2000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0785.certificate15708.rectangle,RoutedCases.Batch0785.certificate15709.rectangle,RoutedCases.Batch0785.certificate15710.rectangle,RoutedCases.Batch0785.certificate15711.rectangle,RoutedCases.Batch0785.certificate15712.rectangle,RoutedCases.Batch0785.certificate15713.rectangle,RoutedCases.Batch0785.certificate15714.rectangle,RoutedCases.Batch0785.certificate15716.rectangle,RoutedCases.Batch0785.certificate15718.rectangle,RoutedCases.Batch0786.certificate15720.rectangle,RoutedCases.Batch0786.certificate15725.rectangle,RoutedCases.Batch0786.certificate15726.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15708,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15710,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15711,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15712,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15713,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15714,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15716,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0785.sound15718,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15720,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15725,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15726,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(53/1000),(107/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source297
