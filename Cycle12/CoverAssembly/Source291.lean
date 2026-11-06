import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0779
import Cycle12.RoutedCases.Batch0780

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source291

def strip0 : RatCoverRectangle := ⟨(99/2000),(397/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0779.certificate15590.rectangle,RoutedCases.Batch0779.certificate15591.rectangle,RoutedCases.Batch0779.certificate15592.rectangle,RoutedCases.Batch0779.certificate15593.rectangle,RoutedCases.Batch0779.certificate15594.rectangle,RoutedCases.Batch0779.certificate15595.rectangle,RoutedCases.Batch0779.certificate15596.rectangle,RoutedCases.Batch0779.certificate15597.rectangle,RoutedCases.Batch0779.certificate15599.rectangle,RoutedCases.Batch0780.certificate15601.rectangle,RoutedCases.Batch0780.certificate15603.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15591,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15593,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15595,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15597,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15603,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(397/8000),(199/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0779.certificate15590.rectangle,RoutedCases.Batch0779.certificate15591.rectangle,RoutedCases.Batch0779.certificate15592.rectangle,RoutedCases.Batch0779.certificate15593.rectangle,RoutedCases.Batch0779.certificate15594.rectangle,RoutedCases.Batch0779.certificate15595.rectangle,RoutedCases.Batch0779.certificate15596.rectangle,RoutedCases.Batch0779.certificate15597.rectangle,RoutedCases.Batch0779.certificate15599.rectangle,RoutedCases.Batch0780.certificate15602.rectangle,RoutedCases.Batch0780.certificate15603.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15591,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15593,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15595,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15597,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15603,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(199/4000),(1/20),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0779.certificate15590.rectangle,RoutedCases.Batch0779.certificate15591.rectangle,RoutedCases.Batch0779.certificate15592.rectangle,RoutedCases.Batch0779.certificate15593.rectangle,RoutedCases.Batch0779.certificate15594.rectangle,RoutedCases.Batch0779.certificate15595.rectangle,RoutedCases.Batch0779.certificate15596.rectangle,RoutedCases.Batch0779.certificate15598.rectangle,RoutedCases.Batch0780.certificate15600.rectangle,RoutedCases.Batch0780.certificate15604.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15590,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15591,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15592,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15593,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15594,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15595,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15596,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0779.sound15598,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15604,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(99/2000),(1/20),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source291
