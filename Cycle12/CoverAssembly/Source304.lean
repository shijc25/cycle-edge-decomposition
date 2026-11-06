import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0794
import Cycle12.RoutedCases.Batch0795

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source304

def strip0 : RatCoverRectangle := ⟨(23/400),(461/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0794.certificate15881.rectangle,RoutedCases.Batch0794.certificate15882.rectangle,RoutedCases.Batch0794.certificate15883.rectangle,RoutedCases.Batch0794.certificate15884.rectangle,RoutedCases.Batch0794.certificate15885.rectangle,RoutedCases.Batch0794.certificate15886.rectangle,RoutedCases.Batch0794.certificate15887.rectangle,RoutedCases.Batch0794.certificate15888.rectangle,RoutedCases.Batch0794.certificate15890.rectangle,RoutedCases.Batch0794.certificate15892.rectangle,RoutedCases.Batch0794.certificate15894.rectangle,RoutedCases.Batch0794.certificate15896.rectangle,RoutedCases.Batch0794.certificate15897.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15883,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15892,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15894,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15896,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15897,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(461/8000),(231/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0794.certificate15881.rectangle,RoutedCases.Batch0794.certificate15882.rectangle,RoutedCases.Batch0794.certificate15883.rectangle,RoutedCases.Batch0794.certificate15884.rectangle,RoutedCases.Batch0794.certificate15885.rectangle,RoutedCases.Batch0794.certificate15886.rectangle,RoutedCases.Batch0794.certificate15887.rectangle,RoutedCases.Batch0794.certificate15888.rectangle,RoutedCases.Batch0794.certificate15890.rectangle,RoutedCases.Batch0794.certificate15892.rectangle,RoutedCases.Batch0794.certificate15895.rectangle,RoutedCases.Batch0794.certificate15898.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15883,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15888,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15890,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15892,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15895,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15898,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(231/4000),(29/500),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0794.certificate15881.rectangle,RoutedCases.Batch0794.certificate15882.rectangle,RoutedCases.Batch0794.certificate15883.rectangle,RoutedCases.Batch0794.certificate15884.rectangle,RoutedCases.Batch0794.certificate15885.rectangle,RoutedCases.Batch0794.certificate15886.rectangle,RoutedCases.Batch0794.certificate15887.rectangle,RoutedCases.Batch0794.certificate15889.rectangle,RoutedCases.Batch0794.certificate15891.rectangle,RoutedCases.Batch0794.certificate15893.rectangle,RoutedCases.Batch0794.certificate15899.rectangle,RoutedCases.Batch0795.certificate15900.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15881,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15882,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15883,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15884,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15885,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15886,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15887,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15889,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15891,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15893,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0794.sound15899,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0795.sound15900,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(23/400),(29/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source304
