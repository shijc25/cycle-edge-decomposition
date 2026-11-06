import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0833
import Cycle12.RoutedCases.Batch0834

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source342

def strip0 : RatCoverRectangle := ⟨(1/80),(51/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0833.certificate16671.rectangle,RoutedCases.Batch0833.certificate16672.rectangle,RoutedCases.Batch0833.certificate16673.rectangle,RoutedCases.Batch0833.certificate16675.rectangle,RoutedCases.Batch0833.certificate16677.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16671,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16672,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16673,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16675,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16677,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(51/4000),(103/8000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0833.certificate16671.rectangle,RoutedCases.Batch0833.certificate16672.rectangle,RoutedCases.Batch0833.certificate16674.rectangle,RoutedCases.Batch0833.certificate16676.rectangle,RoutedCases.Batch0833.certificate16678.rectangle,RoutedCases.Batch0833.certificate16679.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16671,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16672,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16674,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16676,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16678,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16679,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(103/8000),(13/1000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0833.certificate16671.rectangle,RoutedCases.Batch0833.certificate16672.rectangle,RoutedCases.Batch0833.certificate16674.rectangle,RoutedCases.Batch0833.certificate16676.rectangle,RoutedCases.Batch0833.certificate16678.rectangle,RoutedCases.Batch0834.certificate16680.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16671,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16672,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16674,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16676,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0833.sound16678,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16680,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/80),(13/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source342
