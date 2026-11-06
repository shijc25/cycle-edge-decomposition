import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0786

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source298

def strip0 : RatCoverRectangle := ⟨(107/2000),(43/800),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0786.certificate15727.rectangle,RoutedCases.Batch0786.certificate15728.rectangle,RoutedCases.Batch0786.certificate15729.rectangle,RoutedCases.Batch0786.certificate15730.rectangle,RoutedCases.Batch0786.certificate15731.rectangle,RoutedCases.Batch0786.certificate15732.rectangle,RoutedCases.Batch0786.certificate15733.rectangle,RoutedCases.Batch0786.certificate15734.rectangle,RoutedCases.Batch0786.certificate15736.rectangle,RoutedCases.Batch0786.certificate15738.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15727,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15728,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15729,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15734,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15736,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15738,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(43/800),(27/500),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0786.certificate15727.rectangle,RoutedCases.Batch0786.certificate15728.rectangle,RoutedCases.Batch0786.certificate15729.rectangle,RoutedCases.Batch0786.certificate15730.rectangle,RoutedCases.Batch0786.certificate15731.rectangle,RoutedCases.Batch0786.certificate15732.rectangle,RoutedCases.Batch0786.certificate15733.rectangle,RoutedCases.Batch0786.certificate15735.rectangle,RoutedCases.Batch0786.certificate15737.rectangle,RoutedCases.Batch0786.certificate15739.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15727,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15728,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15729,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15730,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15731,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15732,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15733,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15735,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15737,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0786.sound15739,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(107/2000),(27/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source298
