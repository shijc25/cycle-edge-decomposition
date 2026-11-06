import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0780
import Cycle12.RoutedCases.Batch0781

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source292

def strip0 : RatCoverRectangle := ⟨(1/20),(401/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0780.certificate15605.rectangle,RoutedCases.Batch0780.certificate15606.rectangle,RoutedCases.Batch0780.certificate15607.rectangle,RoutedCases.Batch0780.certificate15608.rectangle,RoutedCases.Batch0780.certificate15609.rectangle,RoutedCases.Batch0780.certificate15610.rectangle,RoutedCases.Batch0780.certificate15611.rectangle,RoutedCases.Batch0780.certificate15612.rectangle,RoutedCases.Batch0780.certificate15614.rectangle,RoutedCases.Batch0780.certificate15616.rectangle,RoutedCases.Batch0780.certificate15618.rectangle,RoutedCases.Batch0780.certificate15619.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15605,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15610,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(401/8000),(201/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0780.certificate15605.rectangle,RoutedCases.Batch0780.certificate15606.rectangle,RoutedCases.Batch0780.certificate15607.rectangle,RoutedCases.Batch0780.certificate15608.rectangle,RoutedCases.Batch0780.certificate15609.rectangle,RoutedCases.Batch0780.certificate15610.rectangle,RoutedCases.Batch0780.certificate15611.rectangle,RoutedCases.Batch0780.certificate15612.rectangle,RoutedCases.Batch0780.certificate15614.rectangle,RoutedCases.Batch0780.certificate15616.rectangle,RoutedCases.Batch0780.certificate15618.rectangle,RoutedCases.Batch0781.certificate15620.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15605,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15610,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15616,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15620,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(201/4000),(101/2000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0780.certificate15605.rectangle,RoutedCases.Batch0780.certificate15606.rectangle,RoutedCases.Batch0780.certificate15607.rectangle,RoutedCases.Batch0780.certificate15608.rectangle,RoutedCases.Batch0780.certificate15609.rectangle,RoutedCases.Batch0780.certificate15610.rectangle,RoutedCases.Batch0780.certificate15611.rectangle,RoutedCases.Batch0780.certificate15613.rectangle,RoutedCases.Batch0780.certificate15615.rectangle,RoutedCases.Batch0780.certificate15617.rectangle,RoutedCases.Batch0781.certificate15621.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15605,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15610,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15615,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0780.sound15617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0781.sound15621,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/20),(101/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source292
