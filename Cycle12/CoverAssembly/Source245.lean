import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0711
import Cycle12.RoutedCases.Batch0712

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source245

def strip0 : RatCoverRectangle := ⟨(3/500),(13/2000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0711.certificate14233.rectangle,RoutedCases.Batch0711.certificate14235.rectangle,RoutedCases.Batch0711.certificate14237.rectangle,RoutedCases.Batch0712.certificate14240.rectangle,RoutedCases.Batch0712.certificate14244.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14244,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(13/2000),(27/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0711.certificate14234.rectangle,RoutedCases.Batch0711.certificate14236.rectangle,RoutedCases.Batch0711.certificate14238.rectangle,RoutedCases.Batch0711.certificate14239.rectangle,RoutedCases.Batch0712.certificate14241.rectangle,RoutedCases.Batch0712.certificate14242.rectangle,RoutedCases.Batch0712.certificate14245.rectangle,RoutedCases.Batch0712.certificate14247.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14236,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14241,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14242,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14245,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14247,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(27/4000),(7/1000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0711.certificate14234.rectangle,RoutedCases.Batch0711.certificate14236.rectangle,RoutedCases.Batch0711.certificate14238.rectangle,RoutedCases.Batch0711.certificate14239.rectangle,RoutedCases.Batch0712.certificate14241.rectangle,RoutedCases.Batch0712.certificate14243.rectangle,RoutedCases.Batch0712.certificate14246.rectangle,RoutedCases.Batch0712.certificate14248.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14236,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0711.sound14239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14241,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14246,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14248,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/500),(7/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source245
