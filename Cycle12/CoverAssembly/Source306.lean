import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0796
import Cycle12.RoutedCases.Batch0797

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source306

def strip0 : RatCoverRectangle := ⟨(117/2000),(47/800),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0796.certificate15928.rectangle,RoutedCases.Batch0796.certificate15929.rectangle,RoutedCases.Batch0796.certificate15930.rectangle,RoutedCases.Batch0796.certificate15931.rectangle,RoutedCases.Batch0796.certificate15932.rectangle,RoutedCases.Batch0796.certificate15933.rectangle,RoutedCases.Batch0796.certificate15934.rectangle,RoutedCases.Batch0796.certificate15935.rectangle,RoutedCases.Batch0796.certificate15937.rectangle,RoutedCases.Batch0796.certificate15939.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15933,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15934,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15935,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15937,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15939,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(47/800),(59/1000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0796.certificate15928.rectangle,RoutedCases.Batch0796.certificate15929.rectangle,RoutedCases.Batch0796.certificate15930.rectangle,RoutedCases.Batch0796.certificate15931.rectangle,RoutedCases.Batch0796.certificate15932.rectangle,RoutedCases.Batch0796.certificate15933.rectangle,RoutedCases.Batch0796.certificate15934.rectangle,RoutedCases.Batch0796.certificate15936.rectangle,RoutedCases.Batch0796.certificate15938.rectangle,RoutedCases.Batch0797.certificate15940.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15928,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15929,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15930,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15931,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15932,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15933,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15934,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15936,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0796.sound15938,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0797.sound15940,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(117/2000),(59/1000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source306
