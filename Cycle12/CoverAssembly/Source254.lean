import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0719
import Cycle12.RoutedCases.Batch0720

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source254

def strip0 : RatCoverRectangle := ⟨(13/1000),(53/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0719.certificate14392.rectangle,RoutedCases.Batch0719.certificate14393.rectangle,RoutedCases.Batch0719.certificate14394.rectangle,RoutedCases.Batch0719.certificate14396.rectangle,RoutedCases.Batch0719.certificate14398.rectangle,RoutedCases.Batch0720.certificate14400.rectangle,RoutedCases.Batch0720.certificate14402.rectangle,RoutedCases.Batch0720.certificate14407.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14396,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14398,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14407,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(53/4000),(27/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0719.certificate14392.rectangle,RoutedCases.Batch0719.certificate14393.rectangle,RoutedCases.Batch0719.certificate14394.rectangle,RoutedCases.Batch0719.certificate14396.rectangle,RoutedCases.Batch0719.certificate14398.rectangle,RoutedCases.Batch0720.certificate14400.rectangle,RoutedCases.Batch0720.certificate14402.rectangle,RoutedCases.Batch0720.certificate14408.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14396,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14398,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14408,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(27/2000),(11/800),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0719.certificate14392.rectangle,RoutedCases.Batch0719.certificate14393.rectangle,RoutedCases.Batch0719.certificate14395.rectangle,RoutedCases.Batch0719.certificate14397.rectangle,RoutedCases.Batch0719.certificate14399.rectangle,RoutedCases.Batch0720.certificate14401.rectangle,RoutedCases.Batch0720.certificate14403.rectangle,RoutedCases.Batch0720.certificate14405.rectangle,RoutedCases.Batch0720.certificate14409.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14397,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14399,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14403,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14405,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14409,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(11/800),(111/8000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0719.certificate14392.rectangle,RoutedCases.Batch0719.certificate14393.rectangle,RoutedCases.Batch0719.certificate14395.rectangle,RoutedCases.Batch0719.certificate14397.rectangle,RoutedCases.Batch0719.certificate14399.rectangle,RoutedCases.Batch0720.certificate14401.rectangle,RoutedCases.Batch0720.certificate14404.rectangle,RoutedCases.Batch0720.certificate14406.rectangle,RoutedCases.Batch0720.certificate14410.rectangle,RoutedCases.Batch0720.certificate14411.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14397,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14399,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14404,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14406,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14410,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14411,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(111/8000),(7/500),5,(some 20)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0719.certificate14392.rectangle,RoutedCases.Batch0719.certificate14393.rectangle,RoutedCases.Batch0719.certificate14395.rectangle,RoutedCases.Batch0719.certificate14397.rectangle,RoutedCases.Batch0719.certificate14399.rectangle,RoutedCases.Batch0720.certificate14401.rectangle,RoutedCases.Batch0720.certificate14404.rectangle,RoutedCases.Batch0720.certificate14406.rectangle,RoutedCases.Batch0720.certificate14410.rectangle,RoutedCases.Batch0720.certificate14412.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14397,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14399,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14404,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14406,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14410,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0720.sound14412,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/1000),(7/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source254
