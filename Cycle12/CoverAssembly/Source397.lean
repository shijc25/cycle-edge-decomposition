import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0899
import Cycle12.RoutedCases.Batch0900

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source397

def strip0 : RatCoverRectangle := ⟨(117/2000),(469/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0899.certificate17986.rectangle,RoutedCases.Batch0899.certificate17987.rectangle,RoutedCases.Batch0899.certificate17988.rectangle,RoutedCases.Batch0899.certificate17989.rectangle,RoutedCases.Batch0899.certificate17990.rectangle,RoutedCases.Batch0899.certificate17991.rectangle,RoutedCases.Batch0899.certificate17993.rectangle,RoutedCases.Batch0899.certificate17995.rectangle,RoutedCases.Batch0899.certificate17997.rectangle,RoutedCases.Batch0900.certificate18000.rectangle,RoutedCases.Batch0900.certificate18001.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17995,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17997,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18000,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18001,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(469/8000),(47/800),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0899.certificate17986.rectangle,RoutedCases.Batch0899.certificate17987.rectangle,RoutedCases.Batch0899.certificate17988.rectangle,RoutedCases.Batch0899.certificate17989.rectangle,RoutedCases.Batch0899.certificate17990.rectangle,RoutedCases.Batch0899.certificate17991.rectangle,RoutedCases.Batch0899.certificate17993.rectangle,RoutedCases.Batch0899.certificate17996.rectangle,RoutedCases.Batch0899.certificate17998.rectangle,RoutedCases.Batch0900.certificate18002.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17991,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17993,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17996,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17998,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18002,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(47/800),(59/1000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0899.certificate17986.rectangle,RoutedCases.Batch0899.certificate17987.rectangle,RoutedCases.Batch0899.certificate17988.rectangle,RoutedCases.Batch0899.certificate17989.rectangle,RoutedCases.Batch0899.certificate17990.rectangle,RoutedCases.Batch0899.certificate17992.rectangle,RoutedCases.Batch0899.certificate17994.rectangle,RoutedCases.Batch0899.certificate17999.rectangle,RoutedCases.Batch0900.certificate18003.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17986,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17987,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17988,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17989,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17990,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17992,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17994,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0899.sound17999,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0900.sound18003,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(117/2000),(59/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source397
