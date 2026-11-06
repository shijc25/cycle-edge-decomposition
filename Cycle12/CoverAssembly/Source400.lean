import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0902
import Cycle12.RoutedCases.Batch0903

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source400

def strip0 : RatCoverRectangle := ⟨(3/50),(961/16000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0902.certificate18048.rectangle,RoutedCases.Batch0902.certificate18049.rectangle,RoutedCases.Batch0902.certificate18050.rectangle,RoutedCases.Batch0902.certificate18051.rectangle,RoutedCases.Batch0902.certificate18052.rectangle,RoutedCases.Batch0902.certificate18053.rectangle,RoutedCases.Batch0902.certificate18054.rectangle,RoutedCases.Batch0902.certificate18056.rectangle,RoutedCases.Batch0902.certificate18058.rectangle,RoutedCases.Batch0902.certificate18059.rectangle,RoutedCases.Batch0903.certificate18062.rectangle,RoutedCases.Batch0903.certificate18064.rectangle,RoutedCases.Batch0903.certificate18065.rectangle,RoutedCases.Batch0903.certificate18070.rectangle,RoutedCases.Batch0903.certificate18072.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18062,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18064,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18065,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18072,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(961/16000),(481/8000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0902.certificate18048.rectangle,RoutedCases.Batch0902.certificate18049.rectangle,RoutedCases.Batch0902.certificate18050.rectangle,RoutedCases.Batch0902.certificate18051.rectangle,RoutedCases.Batch0902.certificate18052.rectangle,RoutedCases.Batch0902.certificate18053.rectangle,RoutedCases.Batch0902.certificate18054.rectangle,RoutedCases.Batch0902.certificate18056.rectangle,RoutedCases.Batch0902.certificate18058.rectangle,RoutedCases.Batch0902.certificate18059.rectangle,RoutedCases.Batch0903.certificate18062.rectangle,RoutedCases.Batch0903.certificate18064.rectangle,RoutedCases.Batch0903.certificate18066.rectangle,RoutedCases.Batch0903.certificate18070.rectangle,RoutedCases.Batch0903.certificate18072.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18062,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18064,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18066,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18070,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18072,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(481/8000),(241/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0902.certificate18048.rectangle,RoutedCases.Batch0902.certificate18049.rectangle,RoutedCases.Batch0902.certificate18050.rectangle,RoutedCases.Batch0902.certificate18051.rectangle,RoutedCases.Batch0902.certificate18052.rectangle,RoutedCases.Batch0902.certificate18053.rectangle,RoutedCases.Batch0902.certificate18054.rectangle,RoutedCases.Batch0902.certificate18056.rectangle,RoutedCases.Batch0902.certificate18058.rectangle,RoutedCases.Batch0903.certificate18060.rectangle,RoutedCases.Batch0903.certificate18063.rectangle,RoutedCases.Batch0903.certificate18067.rectangle,RoutedCases.Batch0903.certificate18071.rectangle,RoutedCases.Batch0903.certificate18073.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18060,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18063,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18067,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18071,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18073,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(241/4000),(121/2000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0902.certificate18048.rectangle,RoutedCases.Batch0902.certificate18049.rectangle,RoutedCases.Batch0902.certificate18050.rectangle,RoutedCases.Batch0902.certificate18051.rectangle,RoutedCases.Batch0902.certificate18052.rectangle,RoutedCases.Batch0902.certificate18053.rectangle,RoutedCases.Batch0902.certificate18055.rectangle,RoutedCases.Batch0902.certificate18057.rectangle,RoutedCases.Batch0903.certificate18061.rectangle,RoutedCases.Batch0903.certificate18068.rectangle,RoutedCases.Batch0903.certificate18069.rectangle,RoutedCases.Batch0903.certificate18074.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0902.sound18057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18061,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18068,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18069,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0903.sound18074,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/50),(121/2000),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source400
