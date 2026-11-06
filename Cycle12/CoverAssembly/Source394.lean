import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0897

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source394

def strip0 : RatCoverRectangle := ⟨(57/1000),(457/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0897.certificate17942.rectangle,RoutedCases.Batch0897.certificate17943.rectangle,RoutedCases.Batch0897.certificate17944.rectangle,RoutedCases.Batch0897.certificate17945.rectangle,RoutedCases.Batch0897.certificate17946.rectangle,RoutedCases.Batch0897.certificate17947.rectangle,RoutedCases.Batch0897.certificate17949.rectangle,RoutedCases.Batch0897.certificate17951.rectangle,RoutedCases.Batch0897.certificate17953.rectangle,RoutedCases.Batch0897.certificate17954.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17951,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17953,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17954,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(457/8000),(229/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0897.certificate17942.rectangle,RoutedCases.Batch0897.certificate17943.rectangle,RoutedCases.Batch0897.certificate17944.rectangle,RoutedCases.Batch0897.certificate17945.rectangle,RoutedCases.Batch0897.certificate17946.rectangle,RoutedCases.Batch0897.certificate17947.rectangle,RoutedCases.Batch0897.certificate17949.rectangle,RoutedCases.Batch0897.certificate17951.rectangle,RoutedCases.Batch0897.certificate17953.rectangle,RoutedCases.Batch0897.certificate17955.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17947,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17949,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17951,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17953,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17955,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(229/4000),(23/400),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0897.certificate17942.rectangle,RoutedCases.Batch0897.certificate17943.rectangle,RoutedCases.Batch0897.certificate17944.rectangle,RoutedCases.Batch0897.certificate17945.rectangle,RoutedCases.Batch0897.certificate17946.rectangle,RoutedCases.Batch0897.certificate17948.rectangle,RoutedCases.Batch0897.certificate17950.rectangle,RoutedCases.Batch0897.certificate17952.rectangle,RoutedCases.Batch0897.certificate17956.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17942,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17943,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17944,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17945,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17946,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17948,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17950,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17952,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0897.sound17956,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(57/1000),(23/400),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source394
