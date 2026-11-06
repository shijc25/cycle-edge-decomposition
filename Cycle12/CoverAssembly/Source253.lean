import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0718
import Cycle12.RoutedCases.Batch0719

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source253

def strip0 : RatCoverRectangle := ⟨(3/250),(49/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0718.certificate14364.rectangle,RoutedCases.Batch0718.certificate14365.rectangle,RoutedCases.Batch0718.certificate14366.rectangle,RoutedCases.Batch0718.certificate14367.rectangle,RoutedCases.Batch0718.certificate14368.rectangle,RoutedCases.Batch0718.certificate14370.rectangle,RoutedCases.Batch0718.certificate14372.rectangle,RoutedCases.Batch0718.certificate14375.rectangle,RoutedCases.Batch0719.certificate14380.rectangle,RoutedCases.Batch0719.certificate14382.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14372,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14375,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14380,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14382,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(49/4000),(1/80),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0718.certificate14364.rectangle,RoutedCases.Batch0718.certificate14365.rectangle,RoutedCases.Batch0718.certificate14366.rectangle,RoutedCases.Batch0718.certificate14367.rectangle,RoutedCases.Batch0718.certificate14368.rectangle,RoutedCases.Batch0718.certificate14370.rectangle,RoutedCases.Batch0718.certificate14372.rectangle,RoutedCases.Batch0718.certificate14375.rectangle,RoutedCases.Batch0719.certificate14381.rectangle,RoutedCases.Batch0719.certificate14383.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14372,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14375,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14381,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14383,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(1/80),(51/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0718.certificate14364.rectangle,RoutedCases.Batch0718.certificate14365.rectangle,RoutedCases.Batch0718.certificate14366.rectangle,RoutedCases.Batch0718.certificate14367.rectangle,RoutedCases.Batch0718.certificate14369.rectangle,RoutedCases.Batch0718.certificate14371.rectangle,RoutedCases.Batch0718.certificate14373.rectangle,RoutedCases.Batch0718.certificate14374.rectangle,RoutedCases.Batch0718.certificate14376.rectangle,RoutedCases.Batch0718.certificate14378.rectangle,RoutedCases.Batch0719.certificate14384.rectangle,RoutedCases.Batch0719.certificate14386.rectangle,RoutedCases.Batch0719.certificate14387.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14376,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14378,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14384,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14386,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14387,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(51/4000),(103/8000),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0718.certificate14364.rectangle,RoutedCases.Batch0718.certificate14365.rectangle,RoutedCases.Batch0718.certificate14366.rectangle,RoutedCases.Batch0718.certificate14367.rectangle,RoutedCases.Batch0718.certificate14369.rectangle,RoutedCases.Batch0718.certificate14371.rectangle,RoutedCases.Batch0718.certificate14373.rectangle,RoutedCases.Batch0718.certificate14374.rectangle,RoutedCases.Batch0718.certificate14377.rectangle,RoutedCases.Batch0718.certificate14379.rectangle,RoutedCases.Batch0719.certificate14385.rectangle,RoutedCases.Batch0719.certificate14388.rectangle,RoutedCases.Batch0719.certificate14390.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14377,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14385,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14388,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14390,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(103/8000),(13/1000),5,(some 20)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0718.certificate14364.rectangle,RoutedCases.Batch0718.certificate14365.rectangle,RoutedCases.Batch0718.certificate14366.rectangle,RoutedCases.Batch0718.certificate14367.rectangle,RoutedCases.Batch0718.certificate14369.rectangle,RoutedCases.Batch0718.certificate14371.rectangle,RoutedCases.Batch0718.certificate14373.rectangle,RoutedCases.Batch0718.certificate14374.rectangle,RoutedCases.Batch0718.certificate14377.rectangle,RoutedCases.Batch0718.certificate14379.rectangle,RoutedCases.Batch0719.certificate14385.rectangle,RoutedCases.Batch0719.certificate14389.rectangle,RoutedCases.Batch0719.certificate14391.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14377,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0718.sound14379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14385,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14389,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0719.sound14391,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/250),(13/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source253
