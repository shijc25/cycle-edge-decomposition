import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0439
import Cycle12.RoutedCases.Batch0440

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source144

def strip0 : RatCoverRectangle := ⟨(103/1600),(1031/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0439.certificate8782.rectangle,RoutedCases.Batch0439.certificate8783.rectangle,RoutedCases.Batch0439.certificate8785.rectangle,RoutedCases.Batch0439.certificate8787.rectangle,RoutedCases.Batch0439.certificate8789.rectangle,RoutedCases.Batch0439.certificate8791.rectangle,RoutedCases.Batch0439.certificate8792.rectangle,RoutedCases.Batch0439.certificate8793.rectangle,RoutedCases.Batch0439.certificate8794.rectangle,RoutedCases.Batch0439.certificate8795.rectangle,RoutedCases.Batch0439.certificate8796.rectangle,RoutedCases.Batch0439.certificate8797.rectangle,RoutedCases.Batch0439.certificate8798.rectangle,RoutedCases.Batch0439.certificate8799.rectangle,RoutedCases.Batch0440.certificate8800.rectangle,RoutedCases.Batch0440.certificate8801.rectangle,RoutedCases.Batch0440.certificate8802.rectangle,RoutedCases.Batch0440.certificate8803.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8782,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8783,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8785,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8787,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8789,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8794,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8795,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8796,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8797,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8798,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8799,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8800,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8801,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8802,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8803,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1031/16000),(129/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0439.certificate8784.rectangle,RoutedCases.Batch0439.certificate8786.rectangle,RoutedCases.Batch0439.certificate8788.rectangle,RoutedCases.Batch0439.certificate8790.rectangle,RoutedCases.Batch0439.certificate8791.rectangle,RoutedCases.Batch0439.certificate8792.rectangle,RoutedCases.Batch0439.certificate8793.rectangle,RoutedCases.Batch0439.certificate8794.rectangle,RoutedCases.Batch0439.certificate8795.rectangle,RoutedCases.Batch0439.certificate8796.rectangle,RoutedCases.Batch0439.certificate8797.rectangle,RoutedCases.Batch0439.certificate8798.rectangle,RoutedCases.Batch0439.certificate8799.rectangle,RoutedCases.Batch0440.certificate8800.rectangle,RoutedCases.Batch0440.certificate8801.rectangle,RoutedCases.Batch0440.certificate8802.rectangle,RoutedCases.Batch0440.certificate8803.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8784,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8786,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8788,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8790,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8791,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8792,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8793,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8794,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8795,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8796,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8797,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8798,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0439.sound8799,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8800,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8801,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8802,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0440.sound8803,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(103/1600),(129/2000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source144
