import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0000
import Cycle12.RoutedCases.Batch0001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source003

def strip0 : RatCoverRectangle := ⟨(1/250),(9/2000),1,(some 2)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0000.certificate11.rectangle,RoutedCases.Batch0000.certificate12.rectangle,RoutedCases.Batch0000.certificate17.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound11,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound12,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound17,List.forall_mem_nil _⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(9/2000),(19/4000),1,(some 2)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0000.certificate13.rectangle,RoutedCases.Batch0000.certificate15.rectangle,RoutedCases.Batch0000.certificate18.rectangle,RoutedCases.Batch0001.certificate20.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound13,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound15,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound18,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound20,List.forall_mem_nil _⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(19/4000),(1/200),1,(some 2)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0000.certificate14.rectangle,RoutedCases.Batch0000.certificate16.rectangle,RoutedCases.Batch0000.certificate19.rectangle,RoutedCases.Batch0001.certificate20.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound14,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound16,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0000.sound19,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0001.sound20,List.forall_mem_nil _⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(1/250),(1/200),1,(some 2)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source003
