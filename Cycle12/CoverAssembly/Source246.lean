import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0712
import Cycle12.RoutedCases.Batch0713

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source246

def strip0 : RatCoverRectangle := ⟨(7/1000),(29/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0712.certificate14249.rectangle,RoutedCases.Batch0712.certificate14250.rectangle,RoutedCases.Batch0712.certificate14251.rectangle,RoutedCases.Batch0712.certificate14252.rectangle,RoutedCases.Batch0712.certificate14253.rectangle,RoutedCases.Batch0712.certificate14255.rectangle,RoutedCases.Batch0712.certificate14257.rectangle,RoutedCases.Batch0712.certificate14259.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14259,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(29/4000),(3/400),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0712.certificate14249.rectangle,RoutedCases.Batch0712.certificate14250.rectangle,RoutedCases.Batch0712.certificate14251.rectangle,RoutedCases.Batch0712.certificate14252.rectangle,RoutedCases.Batch0712.certificate14254.rectangle,RoutedCases.Batch0712.certificate14256.rectangle,RoutedCases.Batch0712.certificate14258.rectangle,RoutedCases.Batch0713.certificate14260.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0712.sound14258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0713.sound14260,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(7/1000),(3/400),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source246
