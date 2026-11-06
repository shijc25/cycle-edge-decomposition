import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0778
import Cycle12.RoutedCases.Batch0779

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source290

def strip0 : RatCoverRectangle := ⟨(49/1000),(393/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0778.certificate15573.rectangle,RoutedCases.Batch0778.certificate15574.rectangle,RoutedCases.Batch0778.certificate15575.rectangle,RoutedCases.Batch0778.certificate15576.rectangle,RoutedCases.Batch0778.certificate15577.rectangle,RoutedCases.Batch0778.certificate15578.rectangle,RoutedCases.Batch0778.certificate15579.rectangle,RoutedCases.Batch0779.certificate15580.rectangle,RoutedCases.Batch0779.certificate15582.rectangle,RoutedCases.Batch0779.certificate15584.rectangle,RoutedCases.Batch0779.certificate15586.rectangle,RoutedCases.Batch0779.certificate15587.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15582,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15584,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15586,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(393/8000),(197/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0778.certificate15573.rectangle,RoutedCases.Batch0778.certificate15574.rectangle,RoutedCases.Batch0778.certificate15575.rectangle,RoutedCases.Batch0778.certificate15576.rectangle,RoutedCases.Batch0778.certificate15577.rectangle,RoutedCases.Batch0778.certificate15578.rectangle,RoutedCases.Batch0778.certificate15579.rectangle,RoutedCases.Batch0779.certificate15580.rectangle,RoutedCases.Batch0779.certificate15582.rectangle,RoutedCases.Batch0779.certificate15584.rectangle,RoutedCases.Batch0779.certificate15586.rectangle,RoutedCases.Batch0779.certificate15588.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15582,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15584,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15586,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15588,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(197/4000),(99/2000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0778.certificate15573.rectangle,RoutedCases.Batch0778.certificate15574.rectangle,RoutedCases.Batch0778.certificate15575.rectangle,RoutedCases.Batch0778.certificate15576.rectangle,RoutedCases.Batch0778.certificate15577.rectangle,RoutedCases.Batch0778.certificate15578.rectangle,RoutedCases.Batch0778.certificate15579.rectangle,RoutedCases.Batch0779.certificate15581.rectangle,RoutedCases.Batch0779.certificate15583.rectangle,RoutedCases.Batch0779.certificate15585.rectangle,RoutedCases.Batch0779.certificate15589.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0778.sound15579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15581,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15583,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15585,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15589,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(49/1000),(99/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source290
