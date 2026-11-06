import Cycle12.RationalCoverAssembly
import Cycle12.DirectCases.Batch002
import Cycle12.RoutedCases.Batch1004

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source490

def strip0 : RatCoverRectangle := ⟨(8/125),(13/200),100,none⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch1004.certificate20139.rectangle,RoutedCases.Batch1004.certificate20140.rectangle,RoutedCases.Batch1004.certificate20141.rectangle,RoutedCases.Batch1004.certificate20142.rectangle,RoutedCases.Batch1004.certificate20143.rectangle,RoutedCases.Batch1004.certificate20144.rectangle,RoutedCases.Batch1004.certificate20145.rectangle,RoutedCases.Batch1004.certificate20146.rectangle,RoutedCases.Batch1004.certificate20147.rectangle,DirectCases.Batch002.certificate20148.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20142,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20143,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20144,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20145,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20146,List.forall_mem_cons.mpr ⟨RoutedCases.Batch1004.sound20147,List.forall_mem_cons.mpr ⟨DirectCases.Batch002.sound20148,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(8/125),(13/200),100,none⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source490
