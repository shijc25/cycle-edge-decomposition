import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0910
import Cycle12.RoutedCases.Batch0911

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source405

def strip0 : RatCoverRectangle := ⟨(63/1000),(1009/16000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0910.certificate18207.rectangle,RoutedCases.Batch0910.certificate18208.rectangle,RoutedCases.Batch0910.certificate18209.rectangle,RoutedCases.Batch0910.certificate18210.rectangle,RoutedCases.Batch0910.certificate18211.rectangle,RoutedCases.Batch0910.certificate18213.rectangle,RoutedCases.Batch0910.certificate18215.rectangle,RoutedCases.Batch0910.certificate18217.rectangle,RoutedCases.Batch0910.certificate18219.rectangle,RoutedCases.Batch0911.certificate18220.rectangle,RoutedCases.Batch0911.certificate18223.rectangle,RoutedCases.Batch0911.certificate18225.rectangle,RoutedCases.Batch0911.certificate18226.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18208,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18210,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18211,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18220,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18223,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18225,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18226,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(1009/16000),(101/1600),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0910.certificate18207.rectangle,RoutedCases.Batch0910.certificate18208.rectangle,RoutedCases.Batch0910.certificate18209.rectangle,RoutedCases.Batch0910.certificate18210.rectangle,RoutedCases.Batch0910.certificate18211.rectangle,RoutedCases.Batch0910.certificate18213.rectangle,RoutedCases.Batch0910.certificate18215.rectangle,RoutedCases.Batch0910.certificate18217.rectangle,RoutedCases.Batch0910.certificate18219.rectangle,RoutedCases.Batch0911.certificate18220.rectangle,RoutedCases.Batch0911.certificate18223.rectangle,RoutedCases.Batch0911.certificate18225.rectangle,RoutedCases.Batch0911.certificate18227.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18208,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18210,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18211,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18220,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18223,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18225,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18227,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(101/1600),(253/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0910.certificate18207.rectangle,RoutedCases.Batch0910.certificate18208.rectangle,RoutedCases.Batch0910.certificate18209.rectangle,RoutedCases.Batch0910.certificate18210.rectangle,RoutedCases.Batch0910.certificate18211.rectangle,RoutedCases.Batch0910.certificate18213.rectangle,RoutedCases.Batch0910.certificate18215.rectangle,RoutedCases.Batch0910.certificate18217.rectangle,RoutedCases.Batch0910.certificate18219.rectangle,RoutedCases.Batch0911.certificate18221.rectangle,RoutedCases.Batch0911.certificate18224.rectangle,RoutedCases.Batch0911.certificate18228.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18208,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18210,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18211,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18213,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18215,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18217,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18219,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18221,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18224,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18228,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(253/4000),(127/2000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0910.certificate18207.rectangle,RoutedCases.Batch0910.certificate18208.rectangle,RoutedCases.Batch0910.certificate18209.rectangle,RoutedCases.Batch0910.certificate18210.rectangle,RoutedCases.Batch0910.certificate18212.rectangle,RoutedCases.Batch0910.certificate18214.rectangle,RoutedCases.Batch0910.certificate18216.rectangle,RoutedCases.Batch0910.certificate18218.rectangle,RoutedCases.Batch0911.certificate18222.rectangle,RoutedCases.Batch0911.certificate18229.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18207,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18208,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18209,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18210,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18212,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18214,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18216,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0910.sound18218,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18222,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18229,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(63/1000),(127/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source405
