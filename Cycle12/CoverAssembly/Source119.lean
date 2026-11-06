import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0405
import Cycle12.RoutedCases.Batch0406
import Cycle12.RoutedCases.Batch0407

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source119

def strip0 : RatCoverRectangle := ⟨(3/50),(481/8000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0405.certificate8118.rectangle,RoutedCases.Batch0406.certificate8120.rectangle,RoutedCases.Batch0406.certificate8123.rectangle,RoutedCases.Batch0406.certificate8124.rectangle,RoutedCases.Batch0406.certificate8126.rectangle,RoutedCases.Batch0406.certificate8128.rectangle,RoutedCases.Batch0406.certificate8130.rectangle,RoutedCases.Batch0406.certificate8132.rectangle,RoutedCases.Batch0406.certificate8134.rectangle,RoutedCases.Batch0406.certificate8135.rectangle,RoutedCases.Batch0406.certificate8136.rectangle,RoutedCases.Batch0406.certificate8137.rectangle,RoutedCases.Batch0406.certificate8138.rectangle,RoutedCases.Batch0406.certificate8139.rectangle,RoutedCases.Batch0407.certificate8140.rectangle,RoutedCases.Batch0407.certificate8141.rectangle,RoutedCases.Batch0407.certificate8142.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0405.sound8118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8120,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8124,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8126,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8134,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8138,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8142,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(481/8000),(241/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0405.certificate8119.rectangle,RoutedCases.Batch0406.certificate8121.rectangle,RoutedCases.Batch0406.certificate8123.rectangle,RoutedCases.Batch0406.certificate8124.rectangle,RoutedCases.Batch0406.certificate8126.rectangle,RoutedCases.Batch0406.certificate8128.rectangle,RoutedCases.Batch0406.certificate8130.rectangle,RoutedCases.Batch0406.certificate8132.rectangle,RoutedCases.Batch0406.certificate8134.rectangle,RoutedCases.Batch0406.certificate8135.rectangle,RoutedCases.Batch0406.certificate8136.rectangle,RoutedCases.Batch0406.certificate8137.rectangle,RoutedCases.Batch0406.certificate8138.rectangle,RoutedCases.Batch0406.certificate8139.rectangle,RoutedCases.Batch0407.certificate8140.rectangle,RoutedCases.Batch0407.certificate8141.rectangle,RoutedCases.Batch0407.certificate8142.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0405.sound8119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8124,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8126,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8134,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8138,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8142,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(241/4000),(121/2000),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0406.certificate8122.rectangle,RoutedCases.Batch0406.certificate8125.rectangle,RoutedCases.Batch0406.certificate8127.rectangle,RoutedCases.Batch0406.certificate8129.rectangle,RoutedCases.Batch0406.certificate8131.rectangle,RoutedCases.Batch0406.certificate8133.rectangle,RoutedCases.Batch0406.certificate8134.rectangle,RoutedCases.Batch0406.certificate8135.rectangle,RoutedCases.Batch0406.certificate8136.rectangle,RoutedCases.Batch0406.certificate8137.rectangle,RoutedCases.Batch0406.certificate8138.rectangle,RoutedCases.Batch0406.certificate8139.rectangle,RoutedCases.Batch0407.certificate8140.rectangle,RoutedCases.Batch0407.certificate8141.rectangle,RoutedCases.Batch0407.certificate8142.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8122,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8125,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8127,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8129,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8131,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8133,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8134,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8138,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0406.sound8139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0407.sound8142,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/50),(121/2000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source119
