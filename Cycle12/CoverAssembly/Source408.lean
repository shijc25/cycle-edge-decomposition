import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0913
import Cycle12.RoutedCases.Batch0914

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source408

def strip0 : RatCoverRectangle := ⟨(129/2000),(517/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0913.certificate18270.rectangle,RoutedCases.Batch0913.certificate18271.rectangle,RoutedCases.Batch0913.certificate18272.rectangle,RoutedCases.Batch0913.certificate18273.rectangle,RoutedCases.Batch0913.certificate18274.rectangle,RoutedCases.Batch0913.certificate18276.rectangle,RoutedCases.Batch0913.certificate18278.rectangle,RoutedCases.Batch0914.certificate18280.rectangle,RoutedCases.Batch0914.certificate18283.rectangle,RoutedCases.Batch0914.certificate18285.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18274,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18278,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18280,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18283,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18285,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(517/8000),(259/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0913.certificate18270.rectangle,RoutedCases.Batch0913.certificate18271.rectangle,RoutedCases.Batch0913.certificate18272.rectangle,RoutedCases.Batch0913.certificate18273.rectangle,RoutedCases.Batch0913.certificate18274.rectangle,RoutedCases.Batch0913.certificate18276.rectangle,RoutedCases.Batch0913.certificate18279.rectangle,RoutedCases.Batch0914.certificate18281.rectangle,RoutedCases.Batch0914.certificate18284.rectangle,RoutedCases.Batch0914.certificate18285.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18274,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18276,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18279,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18281,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18284,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18285,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(259/4000),(13/200),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0913.certificate18270.rectangle,RoutedCases.Batch0913.certificate18271.rectangle,RoutedCases.Batch0913.certificate18272.rectangle,RoutedCases.Batch0913.certificate18273.rectangle,RoutedCases.Batch0913.certificate18275.rectangle,RoutedCases.Batch0913.certificate18277.rectangle,RoutedCases.Batch0914.certificate18282.rectangle,RoutedCases.Batch0914.certificate18286.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18270,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18271,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18272,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18273,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18275,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0913.sound18277,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18282,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0914.sound18286,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(129/2000),(13/200),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source408
