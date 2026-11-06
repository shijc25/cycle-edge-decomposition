import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0903
import Cycle12.RoutedCases.Batch0904
import Cycle12.RoutedCases.Batch0905

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source401

def strip0 : RatCoverRectangle := ⟨(121/2000),(969/16000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0903.certificate18075.rectangle,RoutedCases.Batch0903.certificate18076.rectangle,RoutedCases.Batch0903.certificate18077.rectangle,RoutedCases.Batch0903.certificate18078.rectangle,RoutedCases.Batch0903.certificate18079.rectangle,RoutedCases.Batch0904.certificate18081.rectangle,RoutedCases.Batch0904.certificate18083.rectangle,RoutedCases.Batch0904.certificate18085.rectangle,RoutedCases.Batch0904.certificate18087.rectangle,RoutedCases.Batch0904.certificate18089.rectangle,RoutedCases.Batch0904.certificate18092.rectangle,RoutedCases.Batch0904.certificate18093.rectangle,RoutedCases.Batch0904.certificate18096.rectangle,RoutedCases.Batch0904.certificate18098.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18079,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18081,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18083,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18085,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18087,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18089,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18092,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18093,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18096,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18098,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(969/16000),(97/1600),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0903.certificate18075.rectangle,RoutedCases.Batch0903.certificate18076.rectangle,RoutedCases.Batch0903.certificate18077.rectangle,RoutedCases.Batch0903.certificate18078.rectangle,RoutedCases.Batch0903.certificate18079.rectangle,RoutedCases.Batch0904.certificate18081.rectangle,RoutedCases.Batch0904.certificate18083.rectangle,RoutedCases.Batch0904.certificate18085.rectangle,RoutedCases.Batch0904.certificate18087.rectangle,RoutedCases.Batch0904.certificate18089.rectangle,RoutedCases.Batch0904.certificate18092.rectangle,RoutedCases.Batch0904.certificate18094.rectangle,RoutedCases.Batch0904.certificate18097.rectangle,RoutedCases.Batch0904.certificate18099.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18079,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18081,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18083,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18085,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18087,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18089,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18092,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18094,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18097,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18099,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(97/1600),(243/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0903.certificate18075.rectangle,RoutedCases.Batch0903.certificate18076.rectangle,RoutedCases.Batch0903.certificate18077.rectangle,RoutedCases.Batch0903.certificate18078.rectangle,RoutedCases.Batch0903.certificate18079.rectangle,RoutedCases.Batch0904.certificate18081.rectangle,RoutedCases.Batch0904.certificate18083.rectangle,RoutedCases.Batch0904.certificate18085.rectangle,RoutedCases.Batch0904.certificate18088.rectangle,RoutedCases.Batch0904.certificate18090.rectangle,RoutedCases.Batch0904.certificate18095.rectangle,RoutedCases.Batch0905.certificate18100.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18079,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18081,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18083,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18085,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18088,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18090,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18095,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18100,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(243/4000),(487/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0903.certificate18075.rectangle,RoutedCases.Batch0903.certificate18076.rectangle,RoutedCases.Batch0903.certificate18077.rectangle,RoutedCases.Batch0903.certificate18078.rectangle,RoutedCases.Batch0904.certificate18080.rectangle,RoutedCases.Batch0904.certificate18082.rectangle,RoutedCases.Batch0904.certificate18084.rectangle,RoutedCases.Batch0904.certificate18086.rectangle,RoutedCases.Batch0904.certificate18091.rectangle,RoutedCases.Batch0905.certificate18101.rectangle,RoutedCases.Batch0905.certificate18103.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18080,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18082,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18084,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18086,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18091,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18101,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18103,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(487/8000),(61/1000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0903.certificate18075.rectangle,RoutedCases.Batch0903.certificate18076.rectangle,RoutedCases.Batch0903.certificate18077.rectangle,RoutedCases.Batch0903.certificate18078.rectangle,RoutedCases.Batch0904.certificate18080.rectangle,RoutedCases.Batch0904.certificate18082.rectangle,RoutedCases.Batch0904.certificate18084.rectangle,RoutedCases.Batch0904.certificate18086.rectangle,RoutedCases.Batch0904.certificate18091.rectangle,RoutedCases.Batch0905.certificate18102.rectangle,RoutedCases.Batch0905.certificate18104.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18075,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18076,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18077,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18078,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18080,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18082,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18084,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18086,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0904.sound18091,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18102,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0905.sound18104,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(121/2000),(61/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source401
