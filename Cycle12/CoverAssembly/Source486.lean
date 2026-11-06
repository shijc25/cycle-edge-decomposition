import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source486

def strip0 : RatCoverRectangle := ⟨(3/50),(61/1000),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1002.certificate20092.rectangle,RoutedCases.Batch1002.certificate20093.rectangle,RoutedCases.Batch1002.certificate20094.rectangle,RoutedCases.Batch1002.certificate20095.rectangle,RoutedCases.Batch1002.certificate20096.rectangle,RoutedCases.Batch1002.certificate20097.rectangle,RoutedCases.Batch1002.certificate20098.rectangle,RoutedCases.Batch1002.certificate20099.rectangle,RoutedCases.Batch1002.certificate20100.rectangle,RoutedCases.Batch1002.certificate20101.rectangle,RoutedCases.Batch1002.certificate20102.rectangle,RoutedCases.Batch1002.certificate20103.rectangle,DirectCases.Batch002.certificate20104.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20092,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20093,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20094,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20095,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20096,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20097,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20098,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20099,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20100,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20101,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20102,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1002.sound20103,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20104,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/50),(61/1000),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source486
