import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0893

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source391

def strip0 : RatCoverRectangle := ⟨(109/2000),(437/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17863.rectangle,RoutedCases.Batch0893.certificate17864.rectangle,RoutedCases.Batch0893.certificate17865.rectangle,RoutedCases.Batch0893.certificate17866.rectangle,RoutedCases.Batch0893.certificate17867.rectangle,RoutedCases.Batch0893.certificate17869.rectangle,RoutedCases.Batch0893.certificate17871.rectangle,RoutedCases.Batch0893.certificate17872.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17863,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17869,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17871,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17872,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(437/8000),(219/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17863.rectangle,RoutedCases.Batch0893.certificate17864.rectangle,RoutedCases.Batch0893.certificate17865.rectangle,RoutedCases.Batch0893.certificate17866.rectangle,RoutedCases.Batch0893.certificate17867.rectangle,RoutedCases.Batch0893.certificate17869.rectangle,RoutedCases.Batch0893.certificate17871.rectangle,RoutedCases.Batch0893.certificate17873.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17863,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17867,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17869,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17871,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17873,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(219/4000),(11/200),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0893.certificate17863.rectangle,RoutedCases.Batch0893.certificate17864.rectangle,RoutedCases.Batch0893.certificate17865.rectangle,RoutedCases.Batch0893.certificate17866.rectangle,RoutedCases.Batch0893.certificate17868.rectangle,RoutedCases.Batch0893.certificate17870.rectangle,RoutedCases.Batch0893.certificate17874.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17863,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17864,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17865,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17866,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17868,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17870,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0893.sound17874,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(109/2000),(11/200),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source391
