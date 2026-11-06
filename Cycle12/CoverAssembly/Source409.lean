import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0914
import Cycle12.RoutedCases.Batch0915

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source409

def strip0 : RatCoverRectangle := ⟨(13/200),(521/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0914.certificate18287.rectangle,RoutedCases.Batch0914.certificate18288.rectangle,RoutedCases.Batch0914.certificate18289.rectangle,RoutedCases.Batch0914.certificate18290.rectangle,RoutedCases.Batch0914.certificate18291.rectangle,RoutedCases.Batch0914.certificate18292.rectangle,RoutedCases.Batch0914.certificate18294.rectangle,RoutedCases.Batch0914.certificate18296.rectangle,RoutedCases.Batch0914.certificate18297.rectangle,RoutedCases.Batch0915.certificate18300.rectangle,RoutedCases.Batch0915.certificate18302.rectangle,RoutedCases.Batch0915.certificate18304.rectangle,RoutedCases.Batch0915.certificate18305.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18291,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18292,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18297,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18300,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18302,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18305,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(521/8000),(261/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0914.certificate18287.rectangle,RoutedCases.Batch0914.certificate18288.rectangle,RoutedCases.Batch0914.certificate18289.rectangle,RoutedCases.Batch0914.certificate18290.rectangle,RoutedCases.Batch0914.certificate18291.rectangle,RoutedCases.Batch0914.certificate18292.rectangle,RoutedCases.Batch0914.certificate18294.rectangle,RoutedCases.Batch0914.certificate18296.rectangle,RoutedCases.Batch0914.certificate18298.rectangle,RoutedCases.Batch0915.certificate18301.rectangle,RoutedCases.Batch0915.certificate18302.rectangle,RoutedCases.Batch0915.certificate18304.rectangle,RoutedCases.Batch0915.certificate18306.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18291,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18292,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18294,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18296,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18298,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18301,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18302,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18306,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(261/4000),(131/2000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0914.certificate18287.rectangle,RoutedCases.Batch0914.certificate18288.rectangle,RoutedCases.Batch0914.certificate18289.rectangle,RoutedCases.Batch0914.certificate18290.rectangle,RoutedCases.Batch0914.certificate18291.rectangle,RoutedCases.Batch0914.certificate18293.rectangle,RoutedCases.Batch0914.certificate18295.rectangle,RoutedCases.Batch0914.certificate18299.rectangle,RoutedCases.Batch0915.certificate18303.rectangle,RoutedCases.Batch0915.certificate18307.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18287,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18288,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18289,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18290,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18291,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18293,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18295,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18299,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18303,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0915.sound18307,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/200),(131/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source409
