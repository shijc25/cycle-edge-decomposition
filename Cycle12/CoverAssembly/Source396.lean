import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0898
import Cycle12.RoutedCases.Batch0899

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source396

def strip0 : RatCoverRectangle := ⟨(29/500),(233/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0898.certificate17973.rectangle,RoutedCases.Batch0898.certificate17974.rectangle,RoutedCases.Batch0898.certificate17975.rectangle,RoutedCases.Batch0898.certificate17976.rectangle,RoutedCases.Batch0898.certificate17977.rectangle,RoutedCases.Batch0898.certificate17978.rectangle,RoutedCases.Batch0899.certificate17980.rectangle,RoutedCases.Batch0899.certificate17982.rectangle,RoutedCases.Batch0899.certificate17984.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17974,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17975,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17976,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17977,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17978,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17980,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17982,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17984,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(233/4000),(117/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0898.certificate17973.rectangle,RoutedCases.Batch0898.certificate17974.rectangle,RoutedCases.Batch0898.certificate17975.rectangle,RoutedCases.Batch0898.certificate17976.rectangle,RoutedCases.Batch0898.certificate17977.rectangle,RoutedCases.Batch0898.certificate17979.rectangle,RoutedCases.Batch0899.certificate17981.rectangle,RoutedCases.Batch0899.certificate17983.rectangle,RoutedCases.Batch0899.certificate17985.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17973,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17974,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17975,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17976,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17977,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0898.sound17979,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17981,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17983,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17985,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(29/500),(117/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_nil _⟩⟩)

end Cycle12.CoverAssembly.Source396
