import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0830

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source337

def strip0 : RatCoverRectangle := ⟨(19/2000),(39/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0830.certificate16606.rectangle,RoutedCases.Batch0830.certificate16607.rectangle,RoutedCases.Batch0830.certificate16608.rectangle,RoutedCases.Batch0830.certificate16609.rectangle,RoutedCases.Batch0830.certificate16611.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16611,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(39/4000),(1/100),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0830.certificate16606.rectangle,RoutedCases.Batch0830.certificate16607.rectangle,RoutedCases.Batch0830.certificate16608.rectangle,RoutedCases.Batch0830.certificate16610.rectangle,RoutedCases.Batch0830.certificate16612.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16610,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0830.sound16612,List.forall_mem_nil _⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(19/2000),(1/100),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source337
