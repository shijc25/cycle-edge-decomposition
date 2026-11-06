import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0918
import Cycle12.RoutedCases.Batch0919

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source413

def strip0 : RatCoverRectangle := ⟨(67/1000),(537/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0918.certificate18379.rectangle,RoutedCases.Batch0919.certificate18380.rectangle,RoutedCases.Batch0919.certificate18381.rectangle,RoutedCases.Batch0919.certificate18382.rectangle,RoutedCases.Batch0919.certificate18383.rectangle,RoutedCases.Batch0919.certificate18384.rectangle,RoutedCases.Batch0919.certificate18386.rectangle,RoutedCases.Batch0919.certificate18388.rectangle,RoutedCases.Batch0919.certificate18389.rectangle,RoutedCases.Batch0919.certificate18392.rectangle,RoutedCases.Batch0919.certificate18394.rectangle,RoutedCases.Batch0919.certificate18396.rectangle,RoutedCases.Batch0919.certificate18397.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18380,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18381,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18382,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18383,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18384,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18386,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18388,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18389,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18392,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18396,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18397,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(537/8000),(269/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0918.certificate18379.rectangle,RoutedCases.Batch0919.certificate18380.rectangle,RoutedCases.Batch0919.certificate18381.rectangle,RoutedCases.Batch0919.certificate18382.rectangle,RoutedCases.Batch0919.certificate18383.rectangle,RoutedCases.Batch0919.certificate18384.rectangle,RoutedCases.Batch0919.certificate18386.rectangle,RoutedCases.Batch0919.certificate18388.rectangle,RoutedCases.Batch0919.certificate18390.rectangle,RoutedCases.Batch0919.certificate18393.rectangle,RoutedCases.Batch0919.certificate18394.rectangle,RoutedCases.Batch0919.certificate18396.rectangle,RoutedCases.Batch0919.certificate18398.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18380,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18381,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18382,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18383,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18384,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18386,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18388,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18390,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18393,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18394,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18396,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18398,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(269/4000),(27/400),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0918.certificate18379.rectangle,RoutedCases.Batch0919.certificate18380.rectangle,RoutedCases.Batch0919.certificate18381.rectangle,RoutedCases.Batch0919.certificate18382.rectangle,RoutedCases.Batch0919.certificate18383.rectangle,RoutedCases.Batch0919.certificate18385.rectangle,RoutedCases.Batch0919.certificate18387.rectangle,RoutedCases.Batch0919.certificate18391.rectangle,RoutedCases.Batch0919.certificate18395.rectangle,RoutedCases.Batch0919.certificate18399.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18379,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18380,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18381,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18382,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18383,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18385,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18387,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18391,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18395,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0919.sound18399,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(67/1000),(27/400),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source413
