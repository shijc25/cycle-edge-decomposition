import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0841

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source351

def strip0 : RatCoverRectangle := ⟨(19/1000),(77/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16820.rectangle,RoutedCases.Batch0841.certificate16821.rectangle,RoutedCases.Batch0841.certificate16822.rectangle,RoutedCases.Batch0841.certificate16823.rectangle,RoutedCases.Batch0841.certificate16824.rectangle,RoutedCases.Batch0841.certificate16826.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16820,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16821,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16822,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16823,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16824,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16826,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(77/4000),(31/1600),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16820.rectangle,RoutedCases.Batch0841.certificate16821.rectangle,RoutedCases.Batch0841.certificate16822.rectangle,RoutedCases.Batch0841.certificate16823.rectangle,RoutedCases.Batch0841.certificate16825.rectangle,RoutedCases.Batch0841.certificate16827.rectangle,RoutedCases.Batch0841.certificate16828.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16820,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16821,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16822,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16823,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16825,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16828,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(31/1600),(39/2000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16820.rectangle,RoutedCases.Batch0841.certificate16821.rectangle,RoutedCases.Batch0841.certificate16822.rectangle,RoutedCases.Batch0841.certificate16823.rectangle,RoutedCases.Batch0841.certificate16825.rectangle,RoutedCases.Batch0841.certificate16827.rectangle,RoutedCases.Batch0841.certificate16829.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16820,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16821,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16822,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16823,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16825,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16829,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(19/1000),(39/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source351
