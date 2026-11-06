import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0807
import Cycle12.RoutedCases.Batch0808

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source317

def strip0 : RatCoverRectangle := ⟨(63/1000),(101/1600),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0807.certificate16153.rectangle,RoutedCases.Batch0807.certificate16154.rectangle,RoutedCases.Batch0807.certificate16155.rectangle,RoutedCases.Batch0807.certificate16156.rectangle,RoutedCases.Batch0807.certificate16157.rectangle,RoutedCases.Batch0807.certificate16158.rectangle,RoutedCases.Batch0807.certificate16159.rectangle,RoutedCases.Batch0808.certificate16160.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16153,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16154,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16155,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16156,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16157,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16158,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16159,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16160,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(101/1600),(253/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0807.certificate16153.rectangle,RoutedCases.Batch0807.certificate16154.rectangle,RoutedCases.Batch0807.certificate16155.rectangle,RoutedCases.Batch0807.certificate16156.rectangle,RoutedCases.Batch0807.certificate16157.rectangle,RoutedCases.Batch0807.certificate16158.rectangle,RoutedCases.Batch0807.certificate16159.rectangle,RoutedCases.Batch0808.certificate16161.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16153,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16154,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16155,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16156,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16157,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16158,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0807.sound16159,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16161,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(63/1000),(253/4000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source317
