import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0461
import Cycle12.RoutedCases.Batch0462

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source164

def strip0 : RatCoverRectangle := ⟨(107/1600),(1071/16000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0461.certificate9222.rectangle,RoutedCases.Batch0461.certificate9223.rectangle,RoutedCases.Batch0461.certificate9225.rectangle,RoutedCases.Batch0461.certificate9227.rectangle,RoutedCases.Batch0461.certificate9229.rectangle,RoutedCases.Batch0461.certificate9230.rectangle,RoutedCases.Batch0461.certificate9231.rectangle,RoutedCases.Batch0461.certificate9232.rectangle,RoutedCases.Batch0461.certificate9233.rectangle,RoutedCases.Batch0461.certificate9234.rectangle,RoutedCases.Batch0461.certificate9235.rectangle,RoutedCases.Batch0461.certificate9236.rectangle,RoutedCases.Batch0461.certificate9237.rectangle,RoutedCases.Batch0461.certificate9238.rectangle,RoutedCases.Batch0461.certificate9239.rectangle,RoutedCases.Batch0462.certificate9240.rectangle,RoutedCases.Batch0462.certificate9241.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9222,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9223,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9225,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9227,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9229,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9236,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9241,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1071/16000),(67/1000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0461.certificate9224.rectangle,RoutedCases.Batch0461.certificate9226.rectangle,RoutedCases.Batch0461.certificate9228.rectangle,RoutedCases.Batch0461.certificate9229.rectangle,RoutedCases.Batch0461.certificate9230.rectangle,RoutedCases.Batch0461.certificate9231.rectangle,RoutedCases.Batch0461.certificate9232.rectangle,RoutedCases.Batch0461.certificate9233.rectangle,RoutedCases.Batch0461.certificate9234.rectangle,RoutedCases.Batch0461.certificate9235.rectangle,RoutedCases.Batch0461.certificate9236.rectangle,RoutedCases.Batch0461.certificate9237.rectangle,RoutedCases.Batch0461.certificate9238.rectangle,RoutedCases.Batch0461.certificate9239.rectangle,RoutedCases.Batch0462.certificate9240.rectangle,RoutedCases.Batch0462.certificate9241.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9224,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9226,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9228,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9229,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9236,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0461.sound9239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0462.sound9241,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(107/1600),(67/1000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source164
