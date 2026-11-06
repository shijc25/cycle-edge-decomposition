import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source002

def strip0 : RatCoverRectangle := ⟨(3/1000),(7/2000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0000.certificate2.rectangle,RoutedCases.Batch0000.certificate3.rectangle,RoutedCases.Batch0000.certificate8.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound2,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound3,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound8,List.forall_mem_nil _⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(7/2000),(3/800),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0000.certificate4.rectangle,RoutedCases.Batch0000.certificate6.rectangle,RoutedCases.Batch0000.certificate9.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound4,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound6,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound9,List.forall_mem_nil _⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(3/800),(1/250),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0000.certificate5.rectangle,RoutedCases.Batch0000.certificate7.rectangle,RoutedCases.Batch0000.certificate10.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound5,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound7,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound10,List.forall_mem_nil _⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/1000),(1/250),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source002
