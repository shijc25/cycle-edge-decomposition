import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0717
import Cycle12.RoutedCases.Batch0718

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source252

def strip0 : RatCoverRectangle := ⟨(23/2000),(47/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0717.certificate14356.rectangle,RoutedCases.Batch0717.certificate14357.rectangle,RoutedCases.Batch0717.certificate14358.rectangle,RoutedCases.Batch0717.certificate14359.rectangle,RoutedCases.Batch0718.certificate14360.rectangle,RoutedCases.Batch0718.certificate14362.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14356,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14357,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14358,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14359,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14360,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14362,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(47/4000),(3/250),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0717.certificate14356.rectangle,RoutedCases.Batch0717.certificate14357.rectangle,RoutedCases.Batch0717.certificate14358.rectangle,RoutedCases.Batch0717.certificate14359.rectangle,RoutedCases.Batch0718.certificate14361.rectangle,RoutedCases.Batch0718.certificate14363.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14356,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14357,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14358,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0717.sound14359,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14361,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14363,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(23/2000),(3/250),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source252
