import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0920

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source414

def strip0 : RatCoverRectangle := ⟨(27/400),(541/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0920.certificate18400.rectangle,RoutedCases.Batch0920.certificate18401.rectangle,RoutedCases.Batch0920.certificate18402.rectangle,RoutedCases.Batch0920.certificate18403.rectangle,RoutedCases.Batch0920.certificate18404.rectangle,RoutedCases.Batch0920.certificate18405.rectangle,RoutedCases.Batch0920.certificate18407.rectangle,RoutedCases.Batch0920.certificate18409.rectangle,RoutedCases.Batch0920.certificate18411.rectangle,RoutedCases.Batch0920.certificate18413.rectangle,RoutedCases.Batch0920.certificate18415.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18403,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18404,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18405,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18407,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18409,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18411,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18413,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18415,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(541/8000),(271/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0920.certificate18400.rectangle,RoutedCases.Batch0920.certificate18401.rectangle,RoutedCases.Batch0920.certificate18402.rectangle,RoutedCases.Batch0920.certificate18403.rectangle,RoutedCases.Batch0920.certificate18404.rectangle,RoutedCases.Batch0920.certificate18405.rectangle,RoutedCases.Batch0920.certificate18407.rectangle,RoutedCases.Batch0920.certificate18409.rectangle,RoutedCases.Batch0920.certificate18411.rectangle,RoutedCases.Batch0920.certificate18414.rectangle,RoutedCases.Batch0920.certificate18416.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18403,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18404,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18405,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18407,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18409,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18411,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18414,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18416,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(271/4000),(17/250),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0920.certificate18400.rectangle,RoutedCases.Batch0920.certificate18401.rectangle,RoutedCases.Batch0920.certificate18402.rectangle,RoutedCases.Batch0920.certificate18403.rectangle,RoutedCases.Batch0920.certificate18404.rectangle,RoutedCases.Batch0920.certificate18406.rectangle,RoutedCases.Batch0920.certificate18408.rectangle,RoutedCases.Batch0920.certificate18410.rectangle,RoutedCases.Batch0920.certificate18412.rectangle,RoutedCases.Batch0920.certificate18417.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18400,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18401,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18402,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18403,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18404,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18406,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18408,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18410,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18412,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0920.sound18417,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(27/400),(17/250),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source414
