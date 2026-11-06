import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0311
import Cycle12.RoutedCases.Batch0312

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source081

def strip0 : RatCoverRectangle := ⟨(101/2000),(81/1600),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0311.certificate6237.rectangle,RoutedCases.Batch0311.certificate6239.rectangle,RoutedCases.Batch0312.certificate6240.rectangle,RoutedCases.Batch0312.certificate6241.rectangle,RoutedCases.Batch0312.certificate6242.rectangle,RoutedCases.Batch0312.certificate6243.rectangle,RoutedCases.Batch0312.certificate6244.rectangle,RoutedCases.Batch0312.certificate6245.rectangle,RoutedCases.Batch0312.certificate6246.rectangle,RoutedCases.Batch0312.certificate6247.rectangle,RoutedCases.Batch0312.certificate6248.rectangle,RoutedCases.Batch0312.certificate6249.rectangle,RoutedCases.Batch0312.certificate6250.rectangle,RoutedCases.Batch0312.certificate6251.rectangle,RoutedCases.Batch0312.certificate6252.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6241,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6242,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6244,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6245,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6246,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6247,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6252,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(81/1600),(203/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0311.certificate6238.rectangle,RoutedCases.Batch0311.certificate6239.rectangle,RoutedCases.Batch0312.certificate6240.rectangle,RoutedCases.Batch0312.certificate6241.rectangle,RoutedCases.Batch0312.certificate6242.rectangle,RoutedCases.Batch0312.certificate6243.rectangle,RoutedCases.Batch0312.certificate6244.rectangle,RoutedCases.Batch0312.certificate6245.rectangle,RoutedCases.Batch0312.certificate6246.rectangle,RoutedCases.Batch0312.certificate6247.rectangle,RoutedCases.Batch0312.certificate6248.rectangle,RoutedCases.Batch0312.certificate6249.rectangle,RoutedCases.Batch0312.certificate6250.rectangle,RoutedCases.Batch0312.certificate6251.rectangle,RoutedCases.Batch0312.certificate6252.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6241,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6242,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6244,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6245,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6246,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6247,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6248,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6249,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6250,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6251,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0312.sound6252,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(101/2000),(203/4000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source081
