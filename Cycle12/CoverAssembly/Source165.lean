import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0462
import Cycle12.RoutedCases.Batch0463

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source165

def strip0 : RatCoverRectangle := ⟨(67/1000),(537/8000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0462.certificate9242.rectangle,RoutedCases.Batch0462.certificate9244.rectangle,RoutedCases.Batch0462.certificate9247.rectangle,RoutedCases.Batch0462.certificate9248.rectangle,RoutedCases.Batch0462.certificate9250.rectangle,RoutedCases.Batch0462.certificate9252.rectangle,RoutedCases.Batch0462.certificate9254.rectangle,RoutedCases.Batch0462.certificate9255.rectangle,RoutedCases.Batch0462.certificate9256.rectangle,RoutedCases.Batch0462.certificate9257.rectangle,RoutedCases.Batch0462.certificate9258.rectangle,RoutedCases.Batch0462.certificate9259.rectangle,RoutedCases.Batch0463.certificate9260.rectangle,RoutedCases.Batch0463.certificate9261.rectangle,RoutedCases.Batch0463.certificate9262.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9242,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9244,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9247,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9259,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9260,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9262,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(537/8000),(269/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0462.certificate9243.rectangle,RoutedCases.Batch0462.certificate9245.rectangle,RoutedCases.Batch0462.certificate9247.rectangle,RoutedCases.Batch0462.certificate9248.rectangle,RoutedCases.Batch0462.certificate9250.rectangle,RoutedCases.Batch0462.certificate9252.rectangle,RoutedCases.Batch0462.certificate9254.rectangle,RoutedCases.Batch0462.certificate9255.rectangle,RoutedCases.Batch0462.certificate9256.rectangle,RoutedCases.Batch0462.certificate9257.rectangle,RoutedCases.Batch0462.certificate9258.rectangle,RoutedCases.Batch0462.certificate9259.rectangle,RoutedCases.Batch0463.certificate9260.rectangle,RoutedCases.Batch0463.certificate9261.rectangle,RoutedCases.Batch0463.certificate9262.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9245,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9247,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9252,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9259,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9260,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9262,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(269/4000),(27/400),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0462.certificate9246.rectangle,RoutedCases.Batch0462.certificate9249.rectangle,RoutedCases.Batch0462.certificate9251.rectangle,RoutedCases.Batch0462.certificate9253.rectangle,RoutedCases.Batch0462.certificate9254.rectangle,RoutedCases.Batch0462.certificate9255.rectangle,RoutedCases.Batch0462.certificate9256.rectangle,RoutedCases.Batch0462.certificate9257.rectangle,RoutedCases.Batch0462.certificate9258.rectangle,RoutedCases.Batch0462.certificate9259.rectangle,RoutedCases.Batch0463.certificate9260.rectangle,RoutedCases.Batch0463.certificate9261.rectangle,RoutedCases.Batch0463.certificate9262.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9246,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9253,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9254,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9255,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9256,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9257,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9258,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9259,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9260,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9261,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0463.sound9262,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(67/1000),(27/400),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source165
