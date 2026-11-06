import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0838

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source348

def strip0 : RatCoverRectangle := ⟨(33/2000),(67/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0838.certificate16763.rectangle,RoutedCases.Batch0838.certificate16764.rectangle,RoutedCases.Batch0838.certificate16765.rectangle,RoutedCases.Batch0838.certificate16766.rectangle,RoutedCases.Batch0838.certificate16768.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16763,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16764,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16765,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16766,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16768,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(67/4000),(17/1000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0838.certificate16763.rectangle,RoutedCases.Batch0838.certificate16764.rectangle,RoutedCases.Batch0838.certificate16765.rectangle,RoutedCases.Batch0838.certificate16767.rectangle,RoutedCases.Batch0838.certificate16769.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16763,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16764,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16765,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16767,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0838.sound16769,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(33/2000),(17/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source348
