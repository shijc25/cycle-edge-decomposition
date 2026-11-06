import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0782
import Cycle12.RoutedCases.Batch0783

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source295

def strip0 : RatCoverRectangle := ⟨(103/2000),(207/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0782.certificate15654.rectangle,RoutedCases.Batch0782.certificate15655.rectangle,RoutedCases.Batch0782.certificate15656.rectangle,RoutedCases.Batch0782.certificate15657.rectangle,RoutedCases.Batch0782.certificate15658.rectangle,RoutedCases.Batch0782.certificate15659.rectangle,RoutedCases.Batch0783.certificate15660.rectangle,RoutedCases.Batch0783.certificate15661.rectangle,RoutedCases.Batch0783.certificate15663.rectangle,RoutedCases.Batch0783.certificate15665.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15654,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15655,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15656,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15657,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15658,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15659,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15660,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15661,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15663,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15665,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(207/4000),(13/250),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0782.certificate15654.rectangle,RoutedCases.Batch0782.certificate15655.rectangle,RoutedCases.Batch0782.certificate15656.rectangle,RoutedCases.Batch0782.certificate15657.rectangle,RoutedCases.Batch0782.certificate15658.rectangle,RoutedCases.Batch0782.certificate15659.rectangle,RoutedCases.Batch0783.certificate15660.rectangle,RoutedCases.Batch0783.certificate15662.rectangle,RoutedCases.Batch0783.certificate15664.rectangle,RoutedCases.Batch0783.certificate15666.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15654,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15655,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15656,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15657,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15658,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15659,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15660,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15662,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15664,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0783.sound15666,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(103/2000),(13/250),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source295
