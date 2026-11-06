import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0828
import Cycle12.RoutedCases.Batch0829

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source335

def strip0 : RatCoverRectangle := ⟨(1/125),(17/2000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0828.certificate16572.rectangle,RoutedCases.Batch0828.certificate16573.rectangle,RoutedCases.Batch0828.certificate16574.rectangle,RoutedCases.Batch0828.certificate16576.rectangle,RoutedCases.Batch0828.certificate16578.rectangle,RoutedCases.Batch0829.certificate16581.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16581,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(17/2000),(7/800),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0828.certificate16572.rectangle,RoutedCases.Batch0828.certificate16573.rectangle,RoutedCases.Batch0828.certificate16575.rectangle,RoutedCases.Batch0828.certificate16577.rectangle,RoutedCases.Batch0828.certificate16579.rectangle,RoutedCases.Batch0829.certificate16580.rectangle,RoutedCases.Batch0829.certificate16582.rectangle,RoutedCases.Batch0829.certificate16584.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16582,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16584,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(7/800),(71/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0828.certificate16572.rectangle,RoutedCases.Batch0828.certificate16573.rectangle,RoutedCases.Batch0828.certificate16575.rectangle,RoutedCases.Batch0828.certificate16577.rectangle,RoutedCases.Batch0828.certificate16579.rectangle,RoutedCases.Batch0829.certificate16580.rectangle,RoutedCases.Batch0829.certificate16583.rectangle,RoutedCases.Batch0829.certificate16585.rectangle,RoutedCases.Batch0829.certificate16587.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16583,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16585,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(71/8000),(9/1000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0828.certificate16572.rectangle,RoutedCases.Batch0828.certificate16573.rectangle,RoutedCases.Batch0828.certificate16575.rectangle,RoutedCases.Batch0828.certificate16577.rectangle,RoutedCases.Batch0828.certificate16579.rectangle,RoutedCases.Batch0829.certificate16580.rectangle,RoutedCases.Batch0829.certificate16583.rectangle,RoutedCases.Batch0829.certificate16586.rectangle,RoutedCases.Batch0829.certificate16587.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0828.sound16579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16583,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16586,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0829.sound16587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/125),(9/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source335
