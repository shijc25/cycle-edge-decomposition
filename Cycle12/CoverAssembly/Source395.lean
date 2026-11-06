import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0897
import Cycle12.RoutedCases.Batch0898

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source395

def strip0 : RatCoverRectangle := ⟨(23/400),(461/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0897.certificate17957.rectangle,RoutedCases.Batch0897.certificate17958.rectangle,RoutedCases.Batch0897.certificate17959.rectangle,RoutedCases.Batch0898.certificate17960.rectangle,RoutedCases.Batch0898.certificate17961.rectangle,RoutedCases.Batch0898.certificate17962.rectangle,RoutedCases.Batch0898.certificate17964.rectangle,RoutedCases.Batch0898.certificate17966.rectangle,RoutedCases.Batch0898.certificate17969.rectangle,RoutedCases.Batch0898.certificate17970.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17957,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17958,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17959,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17960,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17961,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17962,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17966,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17970,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(461/8000),(231/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0897.certificate17957.rectangle,RoutedCases.Batch0897.certificate17958.rectangle,RoutedCases.Batch0897.certificate17959.rectangle,RoutedCases.Batch0898.certificate17960.rectangle,RoutedCases.Batch0898.certificate17961.rectangle,RoutedCases.Batch0898.certificate17962.rectangle,RoutedCases.Batch0898.certificate17964.rectangle,RoutedCases.Batch0898.certificate17967.rectangle,RoutedCases.Batch0898.certificate17969.rectangle,RoutedCases.Batch0898.certificate17971.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17957,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17958,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17959,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17960,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17961,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17962,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17964,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17967,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17969,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17971,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(231/4000),(29/500),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0897.certificate17957.rectangle,RoutedCases.Batch0897.certificate17958.rectangle,RoutedCases.Batch0897.certificate17959.rectangle,RoutedCases.Batch0898.certificate17960.rectangle,RoutedCases.Batch0898.certificate17961.rectangle,RoutedCases.Batch0898.certificate17963.rectangle,RoutedCases.Batch0898.certificate17965.rectangle,RoutedCases.Batch0898.certificate17968.rectangle,RoutedCases.Batch0898.certificate17972.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17957,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17958,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17959,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17960,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17961,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17963,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17965,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17968,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17972,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(23/400),(29/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source395
