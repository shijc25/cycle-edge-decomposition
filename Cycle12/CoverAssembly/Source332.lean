import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0826
import Cycle12.RoutedCases.Batch0827

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source332

def strip0 : RatCoverRectangle := ⟨(3/500),(13/2000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0826.certificate16538.rectangle,RoutedCases.Batch0826.certificate16539.rectangle,RoutedCases.Batch0827.certificate16540.rectangle,RoutedCases.Batch0827.certificate16542.rectangle,RoutedCases.Batch0827.certificate16544.rectangle,RoutedCases.Batch0827.certificate16546.rectangle,RoutedCases.Batch0827.certificate16551.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16538,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16539,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16540,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16542,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16544,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16546,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16551,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(13/2000),(27/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0826.certificate16538.rectangle,RoutedCases.Batch0826.certificate16539.rectangle,RoutedCases.Batch0827.certificate16541.rectangle,RoutedCases.Batch0827.certificate16543.rectangle,RoutedCases.Batch0827.certificate16545.rectangle,RoutedCases.Batch0827.certificate16547.rectangle,RoutedCases.Batch0827.certificate16549.rectangle,RoutedCases.Batch0827.certificate16552.rectangle,RoutedCases.Batch0827.certificate16554.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16538,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16539,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16541,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16543,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16545,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16547,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16549,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16552,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16554,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(27/4000),(11/1600),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0826.certificate16538.rectangle,RoutedCases.Batch0826.certificate16539.rectangle,RoutedCases.Batch0827.certificate16541.rectangle,RoutedCases.Batch0827.certificate16543.rectangle,RoutedCases.Batch0827.certificate16545.rectangle,RoutedCases.Batch0827.certificate16548.rectangle,RoutedCases.Batch0827.certificate16550.rectangle,RoutedCases.Batch0827.certificate16553.rectangle,RoutedCases.Batch0827.certificate16555.rectangle,RoutedCases.Batch0827.certificate16557.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16538,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16539,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16541,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16543,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16545,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16548,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16555,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16557,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(11/1600),(7/1000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0826.certificate16538.rectangle,RoutedCases.Batch0826.certificate16539.rectangle,RoutedCases.Batch0827.certificate16541.rectangle,RoutedCases.Batch0827.certificate16543.rectangle,RoutedCases.Batch0827.certificate16545.rectangle,RoutedCases.Batch0827.certificate16548.rectangle,RoutedCases.Batch0827.certificate16550.rectangle,RoutedCases.Batch0827.certificate16553.rectangle,RoutedCases.Batch0827.certificate16556.rectangle,RoutedCases.Batch0827.certificate16558.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16538,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0826.sound16539,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16541,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16543,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16545,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16548,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16550,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16553,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16556,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0827.sound16558,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/500),(7/1000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source332
