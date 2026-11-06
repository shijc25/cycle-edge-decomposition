import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0911
import Cycle12.RoutedCases.Batch0912

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source406

def strip0 : RatCoverRectangle := ⟨(127/2000),(509/8000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0911.certificate18230.rectangle,RoutedCases.Batch0911.certificate18231.rectangle,RoutedCases.Batch0911.certificate18232.rectangle,RoutedCases.Batch0911.certificate18233.rectangle,RoutedCases.Batch0911.certificate18234.rectangle,RoutedCases.Batch0911.certificate18235.rectangle,RoutedCases.Batch0911.certificate18237.rectangle,RoutedCases.Batch0911.certificate18239.rectangle,RoutedCases.Batch0912.certificate18240.rectangle,RoutedCases.Batch0912.certificate18243.rectangle,RoutedCases.Batch0912.certificate18245.rectangle,RoutedCases.Batch0912.certificate18246.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18240,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18245,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18246,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(509/8000),(51/800),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0911.certificate18230.rectangle,RoutedCases.Batch0911.certificate18231.rectangle,RoutedCases.Batch0911.certificate18232.rectangle,RoutedCases.Batch0911.certificate18233.rectangle,RoutedCases.Batch0911.certificate18234.rectangle,RoutedCases.Batch0911.certificate18235.rectangle,RoutedCases.Batch0911.certificate18237.rectangle,RoutedCases.Batch0911.certificate18239.rectangle,RoutedCases.Batch0912.certificate18241.rectangle,RoutedCases.Batch0912.certificate18243.rectangle,RoutedCases.Batch0912.certificate18245.rectangle,RoutedCases.Batch0912.certificate18247.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18235,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18237,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18239,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18241,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18243,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18245,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18247,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(51/800),(8/125),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0911.certificate18230.rectangle,RoutedCases.Batch0911.certificate18231.rectangle,RoutedCases.Batch0911.certificate18232.rectangle,RoutedCases.Batch0911.certificate18233.rectangle,RoutedCases.Batch0911.certificate18234.rectangle,RoutedCases.Batch0911.certificate18236.rectangle,RoutedCases.Batch0911.certificate18238.rectangle,RoutedCases.Batch0912.certificate18242.rectangle,RoutedCases.Batch0912.certificate18244.rectangle,RoutedCases.Batch0912.certificate18248.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18230,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18231,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18232,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18233,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18234,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18236,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0911.sound18238,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18242,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18244,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0912.sound18248,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(127/2000),(8/125),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_nil _⟩⟩⟩)

end Cycle12.CoverAssembly.Source406
