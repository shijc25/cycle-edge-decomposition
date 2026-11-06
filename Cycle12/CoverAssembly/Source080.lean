import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0310
import Cycle12.RoutedCases.Batch0311

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source080

def strip0 : RatCoverRectangle := ⟨(201/4000),(403/8000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0310.certificate6211.rectangle,RoutedCases.Batch0310.certificate6212.rectangle,RoutedCases.Batch0310.certificate6214.rectangle,RoutedCases.Batch0310.certificate6216.rectangle,RoutedCases.Batch0310.certificate6218.rectangle,RoutedCases.Batch0311.certificate6220.rectangle,RoutedCases.Batch0311.certificate6222.rectangle,RoutedCases.Batch0311.certificate6223.rectangle,RoutedCases.Batch0311.certificate6224.rectangle,RoutedCases.Batch0311.certificate6225.rectangle,RoutedCases.Batch0311.certificate6226.rectangle,RoutedCases.Batch0311.certificate6227.rectangle,RoutedCases.Batch0311.certificate6228.rectangle,RoutedCases.Batch0311.certificate6229.rectangle,RoutedCases.Batch0311.certificate6230.rectangle,RoutedCases.Batch0311.certificate6231.rectangle,RoutedCases.Batch0311.certificate6232.rectangle,RoutedCases.Batch0311.certificate6233.rectangle,RoutedCases.Batch0311.certificate6234.rectangle,RoutedCases.Batch0311.certificate6235.rectangle,RoutedCases.Batch0311.certificate6236.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6211,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6212,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6214,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6216,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6218,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6220,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6222,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6223,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6224,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6225,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6226,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6227,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6228,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6229,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6236,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(403/8000),(101/2000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0310.certificate6213.rectangle,RoutedCases.Batch0310.certificate6215.rectangle,RoutedCases.Batch0310.certificate6217.rectangle,RoutedCases.Batch0310.certificate6219.rectangle,RoutedCases.Batch0311.certificate6221.rectangle,RoutedCases.Batch0311.certificate6222.rectangle,RoutedCases.Batch0311.certificate6223.rectangle,RoutedCases.Batch0311.certificate6224.rectangle,RoutedCases.Batch0311.certificate6225.rectangle,RoutedCases.Batch0311.certificate6226.rectangle,RoutedCases.Batch0311.certificate6227.rectangle,RoutedCases.Batch0311.certificate6228.rectangle,RoutedCases.Batch0311.certificate6229.rectangle,RoutedCases.Batch0311.certificate6230.rectangle,RoutedCases.Batch0311.certificate6231.rectangle,RoutedCases.Batch0311.certificate6232.rectangle,RoutedCases.Batch0311.certificate6233.rectangle,RoutedCases.Batch0311.certificate6234.rectangle,RoutedCases.Batch0311.certificate6235.rectangle,RoutedCases.Batch0311.certificate6236.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0310.sound6219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6221,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6222,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6223,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6224,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6225,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6226,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6227,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6228,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6229,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0311.sound6236,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(201/4000),(101/2000),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source080
