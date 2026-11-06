import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0815
import Cycle12.RoutedCases.Batch0816

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source323

def strip0 : RatCoverRectangle := ⟨(131/2000),(263/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0815.certificate16309.rectangle,RoutedCases.Batch0815.certificate16310.rectangle,RoutedCases.Batch0815.certificate16311.rectangle,RoutedCases.Batch0815.certificate16312.rectangle,RoutedCases.Batch0815.certificate16313.rectangle,RoutedCases.Batch0815.certificate16314.rectangle,RoutedCases.Batch0815.certificate16315.rectangle,RoutedCases.Batch0815.certificate16316.rectangle,RoutedCases.Batch0815.certificate16317.rectangle,RoutedCases.Batch0815.certificate16319.rectangle,RoutedCases.Batch0816.certificate16321.rectangle,RoutedCases.Batch0816.certificate16323.rectangle,RoutedCases.Batch0816.certificate16325.rectangle,RoutedCases.Batch0816.certificate16327.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16313,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16315,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16317,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16319,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16321,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16323,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16325,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16327,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(263/4000),(33/500),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0815.certificate16309.rectangle,RoutedCases.Batch0815.certificate16310.rectangle,RoutedCases.Batch0815.certificate16311.rectangle,RoutedCases.Batch0815.certificate16312.rectangle,RoutedCases.Batch0815.certificate16313.rectangle,RoutedCases.Batch0815.certificate16314.rectangle,RoutedCases.Batch0815.certificate16315.rectangle,RoutedCases.Batch0815.certificate16316.rectangle,RoutedCases.Batch0815.certificate16318.rectangle,RoutedCases.Batch0816.certificate16320.rectangle,RoutedCases.Batch0816.certificate16322.rectangle,RoutedCases.Batch0816.certificate16324.rectangle,RoutedCases.Batch0816.certificate16326.rectangle,RoutedCases.Batch0816.certificate16328.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16313,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16315,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0815.sound16318,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16320,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16322,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16324,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16326,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0816.sound16328,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(131/2000),(33/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source323
