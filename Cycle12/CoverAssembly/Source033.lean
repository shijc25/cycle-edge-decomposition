import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0104
import Cycle12.RoutedCases.Batch0105
import Cycle12.RoutedCases.Batch0106

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source033

def strip0 : RatCoverRectangle := ⟨(33/1000),(133/4000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0104.certificate2097.rectangle,RoutedCases.Batch0104.certificate2099.rectangle,RoutedCases.Batch0105.certificate2101.rectangle,RoutedCases.Batch0105.certificate2103.rectangle,RoutedCases.Batch0105.certificate2105.rectangle,RoutedCases.Batch0105.certificate2107.rectangle,RoutedCases.Batch0105.certificate2109.rectangle,RoutedCases.Batch0105.certificate2110.rectangle,RoutedCases.Batch0105.certificate2111.rectangle,RoutedCases.Batch0105.certificate2112.rectangle,RoutedCases.Batch0105.certificate2113.rectangle,RoutedCases.Batch0105.certificate2114.rectangle,RoutedCases.Batch0105.certificate2115.rectangle,RoutedCases.Batch0105.certificate2116.rectangle,RoutedCases.Batch0105.certificate2117.rectangle,RoutedCases.Batch0105.certificate2118.rectangle,RoutedCases.Batch0105.certificate2119.rectangle,RoutedCases.Batch0106.certificate2120.rectangle,RoutedCases.Batch0106.certificate2121.rectangle,RoutedCases.Batch0106.certificate2122.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0104.sound2097,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0104.sound2099,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2101,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2103,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2105,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2107,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2109,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2110,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2111,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2112,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2113,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2114,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2115,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2116,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2117,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0106.sound2120,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0106.sound2121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0106.sound2122,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(133/4000),(67/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0104.certificate2098.rectangle,RoutedCases.Batch0105.certificate2100.rectangle,RoutedCases.Batch0105.certificate2102.rectangle,RoutedCases.Batch0105.certificate2104.rectangle,RoutedCases.Batch0105.certificate2106.rectangle,RoutedCases.Batch0105.certificate2108.rectangle,RoutedCases.Batch0105.certificate2109.rectangle,RoutedCases.Batch0105.certificate2110.rectangle,RoutedCases.Batch0105.certificate2111.rectangle,RoutedCases.Batch0105.certificate2112.rectangle,RoutedCases.Batch0105.certificate2113.rectangle,RoutedCases.Batch0105.certificate2114.rectangle,RoutedCases.Batch0105.certificate2115.rectangle,RoutedCases.Batch0105.certificate2116.rectangle,RoutedCases.Batch0105.certificate2117.rectangle,RoutedCases.Batch0105.certificate2118.rectangle,RoutedCases.Batch0105.certificate2119.rectangle,RoutedCases.Batch0106.certificate2120.rectangle,RoutedCases.Batch0106.certificate2121.rectangle,RoutedCases.Batch0106.certificate2122.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0104.sound2098,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2100,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2102,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2104,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2106,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2108,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2109,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2110,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2111,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2112,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2113,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2114,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2115,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2116,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2117,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0105.sound2119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0106.sound2120,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0106.sound2121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0106.sound2122,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(33/1000),(67/2000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source033
