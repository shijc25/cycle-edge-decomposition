import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0878
import Cycle12.RoutedCases.Batch0879

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source380

def strip0 : RatCoverRectangle := ⟨(9/200),(181/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0878.certificate17572.rectangle,RoutedCases.Batch0878.certificate17573.rectangle,RoutedCases.Batch0878.certificate17574.rectangle,RoutedCases.Batch0878.certificate17575.rectangle,RoutedCases.Batch0878.certificate17577.rectangle,RoutedCases.Batch0878.certificate17579.rectangle,RoutedCases.Batch0879.certificate17580.rectangle,RoutedCases.Batch0879.certificate17585.rectangle,RoutedCases.Batch0879.certificate17587.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17580,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17585,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17587,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(181/4000),(91/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0878.certificate17572.rectangle,RoutedCases.Batch0878.certificate17573.rectangle,RoutedCases.Batch0878.certificate17574.rectangle,RoutedCases.Batch0878.certificate17575.rectangle,RoutedCases.Batch0878.certificate17577.rectangle,RoutedCases.Batch0878.certificate17579.rectangle,RoutedCases.Batch0879.certificate17581.rectangle,RoutedCases.Batch0879.certificate17586.rectangle,RoutedCases.Batch0879.certificate17588.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17575,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17577,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17579,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17581,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17586,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17588,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(91/2000),(183/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0878.certificate17572.rectangle,RoutedCases.Batch0878.certificate17573.rectangle,RoutedCases.Batch0878.certificate17574.rectangle,RoutedCases.Batch0878.certificate17576.rectangle,RoutedCases.Batch0878.certificate17578.rectangle,RoutedCases.Batch0879.certificate17582.rectangle,RoutedCases.Batch0879.certificate17583.rectangle,RoutedCases.Batch0879.certificate17589.rectangle,RoutedCases.Batch0879.certificate17591.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17582,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17583,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17589,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17591,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(183/4000),(23/500),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0878.certificate17572.rectangle,RoutedCases.Batch0878.certificate17573.rectangle,RoutedCases.Batch0878.certificate17574.rectangle,RoutedCases.Batch0878.certificate17576.rectangle,RoutedCases.Batch0878.certificate17578.rectangle,RoutedCases.Batch0879.certificate17582.rectangle,RoutedCases.Batch0879.certificate17584.rectangle,RoutedCases.Batch0879.certificate17590.rectangle,RoutedCases.Batch0879.certificate17592.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17572,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17573,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17574,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17576,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0878.sound17578,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17582,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17584,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0879.sound17592,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/200),(23/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source380
