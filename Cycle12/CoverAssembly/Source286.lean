import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0771
import Cycle12.RoutedCases.Batch0772

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source286

def strip0 : RatCoverRectangle := ⟨(9/200),(181/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0771.certificate15431.rectangle,RoutedCases.Batch0771.certificate15432.rectangle,RoutedCases.Batch0771.certificate15433.rectangle,RoutedCases.Batch0771.certificate15434.rectangle,RoutedCases.Batch0771.certificate15435.rectangle,RoutedCases.Batch0771.certificate15436.rectangle,RoutedCases.Batch0771.certificate15437.rectangle,RoutedCases.Batch0771.certificate15439.rectangle,RoutedCases.Batch0772.certificate15441.rectangle,RoutedCases.Batch0772.certificate15443.rectangle,RoutedCases.Batch0772.certificate15444.rectangle,RoutedCases.Batch0772.certificate15448.rectangle,RoutedCases.Batch0772.certificate15450.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15431,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15432,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15433,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15434,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15437,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15439,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15441,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15443,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15444,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15448,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15450,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(181/4000),(91/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0771.certificate15431.rectangle,RoutedCases.Batch0771.certificate15432.rectangle,RoutedCases.Batch0771.certificate15433.rectangle,RoutedCases.Batch0771.certificate15434.rectangle,RoutedCases.Batch0771.certificate15435.rectangle,RoutedCases.Batch0771.certificate15436.rectangle,RoutedCases.Batch0771.certificate15437.rectangle,RoutedCases.Batch0771.certificate15439.rectangle,RoutedCases.Batch0772.certificate15441.rectangle,RoutedCases.Batch0772.certificate15443.rectangle,RoutedCases.Batch0772.certificate15445.rectangle,RoutedCases.Batch0772.certificate15449.rectangle,RoutedCases.Batch0772.certificate15451.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15431,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15432,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15433,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15434,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15437,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15439,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15441,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15443,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15445,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15449,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15451,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(91/2000),(183/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0771.certificate15431.rectangle,RoutedCases.Batch0771.certificate15432.rectangle,RoutedCases.Batch0771.certificate15433.rectangle,RoutedCases.Batch0771.certificate15434.rectangle,RoutedCases.Batch0771.certificate15435.rectangle,RoutedCases.Batch0771.certificate15436.rectangle,RoutedCases.Batch0771.certificate15438.rectangle,RoutedCases.Batch0772.certificate15440.rectangle,RoutedCases.Batch0772.certificate15442.rectangle,RoutedCases.Batch0772.certificate15446.rectangle,RoutedCases.Batch0772.certificate15447.rectangle,RoutedCases.Batch0772.certificate15452.rectangle,RoutedCases.Batch0772.certificate15454.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15431,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15432,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15433,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15434,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15438,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15440,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15442,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15446,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15447,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15452,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15454,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(183/4000),(23/500),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0771.certificate15431.rectangle,RoutedCases.Batch0771.certificate15432.rectangle,RoutedCases.Batch0771.certificate15433.rectangle,RoutedCases.Batch0771.certificate15434.rectangle,RoutedCases.Batch0771.certificate15435.rectangle,RoutedCases.Batch0771.certificate15436.rectangle,RoutedCases.Batch0771.certificate15438.rectangle,RoutedCases.Batch0772.certificate15440.rectangle,RoutedCases.Batch0772.certificate15442.rectangle,RoutedCases.Batch0772.certificate15446.rectangle,RoutedCases.Batch0772.certificate15447.rectangle,RoutedCases.Batch0772.certificate15453.rectangle,RoutedCases.Batch0772.certificate15455.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15431,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15432,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15433,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15434,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15435,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15436,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0771.sound15438,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15440,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15442,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15446,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15447,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15453,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0772.sound15455,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/200),(23/500),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source286
