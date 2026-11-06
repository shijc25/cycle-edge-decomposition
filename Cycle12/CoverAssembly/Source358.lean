import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0845
import Cycle12.RoutedCases.Batch0846

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source358

def strip0 : RatCoverRectangle := ⟨(47/2000),(19/800),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0845.certificate16911.rectangle,RoutedCases.Batch0845.certificate16912.rectangle,RoutedCases.Batch0845.certificate16913.rectangle,RoutedCases.Batch0845.certificate16914.rectangle,RoutedCases.Batch0845.certificate16915.rectangle,RoutedCases.Batch0845.certificate16917.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16911,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16912,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16913,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16914,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16915,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16917,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(19/800),(191/8000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0845.certificate16911.rectangle,RoutedCases.Batch0845.certificate16912.rectangle,RoutedCases.Batch0845.certificate16913.rectangle,RoutedCases.Batch0845.certificate16914.rectangle,RoutedCases.Batch0845.certificate16916.rectangle,RoutedCases.Batch0845.certificate16918.rectangle,RoutedCases.Batch0846.certificate16920.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16911,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16912,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16913,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16914,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16916,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16918,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16920,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(191/8000),(3/125),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0845.certificate16911.rectangle,RoutedCases.Batch0845.certificate16912.rectangle,RoutedCases.Batch0845.certificate16913.rectangle,RoutedCases.Batch0845.certificate16914.rectangle,RoutedCases.Batch0845.certificate16916.rectangle,RoutedCases.Batch0845.certificate16919.rectangle,RoutedCases.Batch0846.certificate16920.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16911,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16912,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16913,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16914,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16916,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0845.sound16919,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0846.sound16920,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(47/2000),(3/125),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source358
