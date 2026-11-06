import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0792
import Cycle12.RoutedCases.Batch0793

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source302

def strip0 : RatCoverRectangle := ⟨(113/2000),(453/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0792.certificate15844.rectangle,RoutedCases.Batch0792.certificate15845.rectangle,RoutedCases.Batch0792.certificate15846.rectangle,RoutedCases.Batch0792.certificate15847.rectangle,RoutedCases.Batch0792.certificate15848.rectangle,RoutedCases.Batch0792.certificate15849.rectangle,RoutedCases.Batch0792.certificate15850.rectangle,RoutedCases.Batch0792.certificate15851.rectangle,RoutedCases.Batch0792.certificate15852.rectangle,RoutedCases.Batch0792.certificate15854.rectangle,RoutedCases.Batch0792.certificate15856.rectangle,RoutedCases.Batch0792.certificate15857.rectangle,RoutedCases.Batch0793.certificate15860.rectangle,RoutedCases.Batch0793.certificate15861.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15846,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15847,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15848,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15849,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15850,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15851,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15852,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15854,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15856,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15857,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15861,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(453/8000),(227/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0792.certificate15844.rectangle,RoutedCases.Batch0792.certificate15845.rectangle,RoutedCases.Batch0792.certificate15846.rectangle,RoutedCases.Batch0792.certificate15847.rectangle,RoutedCases.Batch0792.certificate15848.rectangle,RoutedCases.Batch0792.certificate15849.rectangle,RoutedCases.Batch0792.certificate15850.rectangle,RoutedCases.Batch0792.certificate15851.rectangle,RoutedCases.Batch0792.certificate15852.rectangle,RoutedCases.Batch0792.certificate15854.rectangle,RoutedCases.Batch0792.certificate15856.rectangle,RoutedCases.Batch0792.certificate15858.rectangle,RoutedCases.Batch0793.certificate15860.rectangle,RoutedCases.Batch0793.certificate15862.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15846,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15847,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15848,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15849,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15850,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15851,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15852,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15854,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15856,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15858,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15860,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15862,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(227/4000),(57/1000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0792.certificate15844.rectangle,RoutedCases.Batch0792.certificate15845.rectangle,RoutedCases.Batch0792.certificate15846.rectangle,RoutedCases.Batch0792.certificate15847.rectangle,RoutedCases.Batch0792.certificate15848.rectangle,RoutedCases.Batch0792.certificate15849.rectangle,RoutedCases.Batch0792.certificate15850.rectangle,RoutedCases.Batch0792.certificate15851.rectangle,RoutedCases.Batch0792.certificate15853.rectangle,RoutedCases.Batch0792.certificate15855.rectangle,RoutedCases.Batch0792.certificate15859.rectangle,RoutedCases.Batch0793.certificate15863.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15844,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15845,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15846,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15847,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15848,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15849,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15850,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15851,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15853,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15855,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0792.sound15859,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0793.sound15863,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(113/2000),(57/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source302
