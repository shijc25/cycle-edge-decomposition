import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0806
import Cycle12.RoutedCases.Batch0807

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source315

def strip0 : RatCoverRectangle := ⟨(1/16),(501/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0806.certificate16135.rectangle,RoutedCases.Batch0806.certificate16136.rectangle,RoutedCases.Batch0806.certificate16137.rectangle,RoutedCases.Batch0806.certificate16138.rectangle,RoutedCases.Batch0806.certificate16139.rectangle,RoutedCases.Batch0807.certificate16140.rectangle,RoutedCases.Batch0807.certificate16141.rectangle,RoutedCases.Batch0807.certificate16142.rectangle,RoutedCases.Batch0807.certificate16143.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16138,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16142,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16143,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(501/8000),(251/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0806.certificate16135.rectangle,RoutedCases.Batch0806.certificate16136.rectangle,RoutedCases.Batch0806.certificate16137.rectangle,RoutedCases.Batch0806.certificate16138.rectangle,RoutedCases.Batch0806.certificate16139.rectangle,RoutedCases.Batch0807.certificate16140.rectangle,RoutedCases.Batch0807.certificate16141.rectangle,RoutedCases.Batch0807.certificate16142.rectangle,RoutedCases.Batch0807.certificate16144.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16138,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16142,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16144,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/16),(251/4000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source315
