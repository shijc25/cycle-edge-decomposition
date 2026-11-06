import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0906
import Cycle12.RoutedCases.Batch0907

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source403

def strip0 : RatCoverRectangle := ⟨(123/2000),(493/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0906.certificate18127.rectangle,RoutedCases.Batch0906.certificate18128.rectangle,RoutedCases.Batch0906.certificate18129.rectangle,RoutedCases.Batch0906.certificate18130.rectangle,RoutedCases.Batch0906.certificate18131.rectangle,RoutedCases.Batch0906.certificate18132.rectangle,RoutedCases.Batch0906.certificate18133.rectangle,RoutedCases.Batch0906.certificate18135.rectangle,RoutedCases.Batch0906.certificate18137.rectangle,RoutedCases.Batch0906.certificate18138.rectangle,RoutedCases.Batch0907.certificate18141.rectangle,RoutedCases.Batch0907.certificate18143.rectangle,RoutedCases.Batch0907.certificate18146.rectangle,RoutedCases.Batch0907.certificate18148.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18127,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18129,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18131,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18133,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18138,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18141,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18143,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18146,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18148,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(493/8000),(247/4000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0906.certificate18127.rectangle,RoutedCases.Batch0906.certificate18128.rectangle,RoutedCases.Batch0906.certificate18129.rectangle,RoutedCases.Batch0906.certificate18130.rectangle,RoutedCases.Batch0906.certificate18131.rectangle,RoutedCases.Batch0906.certificate18132.rectangle,RoutedCases.Batch0906.certificate18133.rectangle,RoutedCases.Batch0906.certificate18135.rectangle,RoutedCases.Batch0906.certificate18137.rectangle,RoutedCases.Batch0906.certificate18139.rectangle,RoutedCases.Batch0907.certificate18142.rectangle,RoutedCases.Batch0907.certificate18144.rectangle,RoutedCases.Batch0907.certificate18147.rectangle,RoutedCases.Batch0907.certificate18149.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18127,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18129,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18131,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18133,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18135,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18137,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18139,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18142,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18144,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18147,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18149,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(247/4000),(31/500),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0906.certificate18127.rectangle,RoutedCases.Batch0906.certificate18128.rectangle,RoutedCases.Batch0906.certificate18129.rectangle,RoutedCases.Batch0906.certificate18130.rectangle,RoutedCases.Batch0906.certificate18131.rectangle,RoutedCases.Batch0906.certificate18132.rectangle,RoutedCases.Batch0906.certificate18134.rectangle,RoutedCases.Batch0906.certificate18136.rectangle,RoutedCases.Batch0907.certificate18140.rectangle,RoutedCases.Batch0907.certificate18145.rectangle,RoutedCases.Batch0907.certificate18150.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18127,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18128,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18129,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18130,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18131,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18132,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18134,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0906.sound18136,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18140,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18145,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0907.sound18150,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(123/2000),(31/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source403
