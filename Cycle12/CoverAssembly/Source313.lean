import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0805
import Cycle12.RoutedCases.Batch0806

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source313

def strip0 : RatCoverRectangle := ⟨(31/500),(497/8000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0805.certificate16118.rectangle,RoutedCases.Batch0805.certificate16119.rectangle,RoutedCases.Batch0806.certificate16120.rectangle,RoutedCases.Batch0806.certificate16121.rectangle,RoutedCases.Batch0806.certificate16122.rectangle,RoutedCases.Batch0806.certificate16123.rectangle,RoutedCases.Batch0806.certificate16124.rectangle,RoutedCases.Batch0806.certificate16125.rectangle,RoutedCases.Batch0806.certificate16126.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0805.sound16118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0805.sound16119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16120,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16122,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16124,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16125,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16126,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(497/8000),(249/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0805.certificate16118.rectangle,RoutedCases.Batch0805.certificate16119.rectangle,RoutedCases.Batch0806.certificate16120.rectangle,RoutedCases.Batch0806.certificate16121.rectangle,RoutedCases.Batch0806.certificate16122.rectangle,RoutedCases.Batch0806.certificate16123.rectangle,RoutedCases.Batch0806.certificate16124.rectangle,RoutedCases.Batch0806.certificate16125.rectangle,RoutedCases.Batch0806.certificate16127.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0805.sound16118,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0805.sound16119,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16120,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16121,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16122,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16123,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16124,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16125,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0806.sound16127,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(31/500),(249/4000),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source313
