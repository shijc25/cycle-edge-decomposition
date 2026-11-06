import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0781
import Cycle12.RoutedCases.Batch0782

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source294

def strip0 : RatCoverRectangle := ⟨(51/1000),(409/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0781.certificate15637.rectangle,RoutedCases.Batch0781.certificate15638.rectangle,RoutedCases.Batch0781.certificate15639.rectangle,RoutedCases.Batch0782.certificate15640.rectangle,RoutedCases.Batch0782.certificate15641.rectangle,RoutedCases.Batch0782.certificate15642.rectangle,RoutedCases.Batch0782.certificate15643.rectangle,RoutedCases.Batch0782.certificate15644.rectangle,RoutedCases.Batch0782.certificate15646.rectangle,RoutedCases.Batch0782.certificate15648.rectangle,RoutedCases.Batch0782.certificate15650.rectangle,RoutedCases.Batch0782.certificate15651.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15648,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15651,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(409/8000),(41/800),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0781.certificate15637.rectangle,RoutedCases.Batch0781.certificate15638.rectangle,RoutedCases.Batch0781.certificate15639.rectangle,RoutedCases.Batch0782.certificate15640.rectangle,RoutedCases.Batch0782.certificate15641.rectangle,RoutedCases.Batch0782.certificate15642.rectangle,RoutedCases.Batch0782.certificate15643.rectangle,RoutedCases.Batch0782.certificate15644.rectangle,RoutedCases.Batch0782.certificate15646.rectangle,RoutedCases.Batch0782.certificate15648.rectangle,RoutedCases.Batch0782.certificate15650.rectangle,RoutedCases.Batch0782.certificate15652.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15644,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15646,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15648,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15650,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15652,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(41/800),(103/2000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0781.certificate15637.rectangle,RoutedCases.Batch0781.certificate15638.rectangle,RoutedCases.Batch0781.certificate15639.rectangle,RoutedCases.Batch0782.certificate15640.rectangle,RoutedCases.Batch0782.certificate15641.rectangle,RoutedCases.Batch0782.certificate15642.rectangle,RoutedCases.Batch0782.certificate15643.rectangle,RoutedCases.Batch0782.certificate15645.rectangle,RoutedCases.Batch0782.certificate15647.rectangle,RoutedCases.Batch0782.certificate15649.rectangle,RoutedCases.Batch0782.certificate15653.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15637,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15638,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15639,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15640,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15641,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15642,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15643,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15645,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15647,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15649,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0782.sound15653,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(51/1000),(103/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source294
