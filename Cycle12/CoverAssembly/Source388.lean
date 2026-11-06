import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0891
import Cycle12.RoutedCases.Batch0892

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source388

def strip0 : RatCoverRectangle := ⟨(53/1000),(17/320),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0891.certificate17827.rectangle,RoutedCases.Batch0891.certificate17828.rectangle,RoutedCases.Batch0891.certificate17829.rectangle,RoutedCases.Batch0891.certificate17830.rectangle,RoutedCases.Batch0891.certificate17831.rectangle,RoutedCases.Batch0891.certificate17832.rectangle,RoutedCases.Batch0891.certificate17834.rectangle,RoutedCases.Batch0891.certificate17836.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17828,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17834,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17836,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(17/320),(213/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0891.certificate17827.rectangle,RoutedCases.Batch0891.certificate17828.rectangle,RoutedCases.Batch0891.certificate17829.rectangle,RoutedCases.Batch0891.certificate17830.rectangle,RoutedCases.Batch0891.certificate17831.rectangle,RoutedCases.Batch0891.certificate17832.rectangle,RoutedCases.Batch0891.certificate17835.rectangle,RoutedCases.Batch0891.certificate17837.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17828,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17832,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17835,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17837,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(213/4000),(427/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0891.certificate17827.rectangle,RoutedCases.Batch0891.certificate17828.rectangle,RoutedCases.Batch0891.certificate17829.rectangle,RoutedCases.Batch0891.certificate17830.rectangle,RoutedCases.Batch0891.certificate17831.rectangle,RoutedCases.Batch0891.certificate17833.rectangle,RoutedCases.Batch0891.certificate17838.rectangle,RoutedCases.Batch0891.certificate17839.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17828,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17839,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(427/8000),(107/2000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0891.certificate17827.rectangle,RoutedCases.Batch0891.certificate17828.rectangle,RoutedCases.Batch0891.certificate17829.rectangle,RoutedCases.Batch0891.certificate17830.rectangle,RoutedCases.Batch0891.certificate17831.rectangle,RoutedCases.Batch0891.certificate17833.rectangle,RoutedCases.Batch0891.certificate17838.rectangle,RoutedCases.Batch0892.certificate17840.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17827,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17828,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17829,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17830,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17831,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17833,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0891.sound17838,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0892.sound17840,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(53/1000),(107/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source388
