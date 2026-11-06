import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0808

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source318

def strip0 : RatCoverRectangle := ⟨(253/4000),(127/2000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0808.certificate16162.rectangle,RoutedCases.Batch0808.certificate16163.rectangle,RoutedCases.Batch0808.certificate16164.rectangle,RoutedCases.Batch0808.certificate16165.rectangle,RoutedCases.Batch0808.certificate16166.rectangle,RoutedCases.Batch0808.certificate16167.rectangle,RoutedCases.Batch0808.certificate16168.rectangle,RoutedCases.Batch0808.certificate16169.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16162,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16163,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16164,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16165,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16166,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16167,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16168,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0808.sound16169,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(253/4000),(127/2000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_nil _⟩)

end Cycle12.CoverAssembly.Source318
