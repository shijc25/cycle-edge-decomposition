import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0892

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source389

def strip0 : RatCoverRectangle := ⟨(107/2000),(43/800),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0892.certificate17841.rectangle,RoutedCases.Batch0892.certificate17842.rectangle,RoutedCases.Batch0892.certificate17843.rectangle,RoutedCases.Batch0892.certificate17844.rectangle,RoutedCases.Batch0892.certificate17845.rectangle,RoutedCases.Batch0892.certificate17847.rectangle,RoutedCases.Batch0892.certificate17849.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17847,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17849,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(43/800),(27/500),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0892.certificate17841.rectangle,RoutedCases.Batch0892.certificate17842.rectangle,RoutedCases.Batch0892.certificate17843.rectangle,RoutedCases.Batch0892.certificate17844.rectangle,RoutedCases.Batch0892.certificate17846.rectangle,RoutedCases.Batch0892.certificate17848.rectangle,RoutedCases.Batch0892.certificate17850.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17841,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17842,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17843,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17846,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17848,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17850,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(107/2000),(27/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source389
