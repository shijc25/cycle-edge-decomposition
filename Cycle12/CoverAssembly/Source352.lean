import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0841

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source352

def strip0 : RatCoverRectangle := ⟨(39/2000),(79/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16830.rectangle,RoutedCases.Batch0841.certificate16831.rectangle,RoutedCases.Batch0841.certificate16832.rectangle,RoutedCases.Batch0841.certificate16833.rectangle,RoutedCases.Batch0841.certificate16835.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16835,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(79/4000),(159/8000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16830.rectangle,RoutedCases.Batch0841.certificate16831.rectangle,RoutedCases.Batch0841.certificate16832.rectangle,RoutedCases.Batch0841.certificate16834.rectangle,RoutedCases.Batch0841.certificate16836.rectangle,RoutedCases.Batch0841.certificate16838.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16836,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16838,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(159/8000),(1/50),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0841.certificate16830.rectangle,RoutedCases.Batch0841.certificate16831.rectangle,RoutedCases.Batch0841.certificate16832.rectangle,RoutedCases.Batch0841.certificate16834.rectangle,RoutedCases.Batch0841.certificate16837.rectangle,RoutedCases.Batch0841.certificate16838.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16837,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0841.sound16838,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(39/2000),(1/50),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source352
