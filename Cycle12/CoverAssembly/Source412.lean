import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0918

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source412

def strip0 : RatCoverRectangle := ⟨(133/2000),(533/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0918.certificate18364.rectangle,RoutedCases.Batch0918.certificate18365.rectangle,RoutedCases.Batch0918.certificate18366.rectangle,RoutedCases.Batch0918.certificate18367.rectangle,RoutedCases.Batch0918.certificate18368.rectangle,RoutedCases.Batch0918.certificate18370.rectangle,RoutedCases.Batch0918.certificate18372.rectangle,RoutedCases.Batch0918.certificate18374.rectangle,RoutedCases.Batch0918.certificate18376.rectangle,RoutedCases.Batch0918.certificate18377.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18372,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18376,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18377,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(533/8000),(267/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0918.certificate18364.rectangle,RoutedCases.Batch0918.certificate18365.rectangle,RoutedCases.Batch0918.certificate18366.rectangle,RoutedCases.Batch0918.certificate18367.rectangle,RoutedCases.Batch0918.certificate18368.rectangle,RoutedCases.Batch0918.certificate18370.rectangle,RoutedCases.Batch0918.certificate18373.rectangle,RoutedCases.Batch0918.certificate18374.rectangle,RoutedCases.Batch0918.certificate18376.rectangle,RoutedCases.Batch0918.certificate18377.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18368,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18370,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18373,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18374,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18376,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18377,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(267/4000),(67/1000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0918.certificate18364.rectangle,RoutedCases.Batch0918.certificate18365.rectangle,RoutedCases.Batch0918.certificate18366.rectangle,RoutedCases.Batch0918.certificate18367.rectangle,RoutedCases.Batch0918.certificate18369.rectangle,RoutedCases.Batch0918.certificate18371.rectangle,RoutedCases.Batch0918.certificate18375.rectangle,RoutedCases.Batch0918.certificate18378.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18364,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18365,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18366,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18367,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18369,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18371,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18375,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0918.sound18378,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(133/2000),(67/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source412
