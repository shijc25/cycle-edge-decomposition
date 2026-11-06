import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0852
import Cycle12.RoutedCases.Batch0853

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source364

def strip0 : RatCoverRectangle := ⟨(29/1000),(117/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0852.certificate17041.rectangle,RoutedCases.Batch0852.certificate17042.rectangle,RoutedCases.Batch0852.certificate17043.rectangle,RoutedCases.Batch0852.certificate17044.rectangle,RoutedCases.Batch0852.certificate17045.rectangle,RoutedCases.Batch0852.certificate17047.rectangle,RoutedCases.Batch0852.certificate17049.rectangle,RoutedCases.Batch0852.certificate17051.rectangle,RoutedCases.Batch0852.certificate17052.rectangle,RoutedCases.Batch0852.certificate17058.rectangle,RoutedCases.Batch0853.certificate17060.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17043,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17045,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17047,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17052,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17058,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17060,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(117/4000),(59/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0852.certificate17041.rectangle,RoutedCases.Batch0852.certificate17042.rectangle,RoutedCases.Batch0852.certificate17043.rectangle,RoutedCases.Batch0852.certificate17044.rectangle,RoutedCases.Batch0852.certificate17045.rectangle,RoutedCases.Batch0852.certificate17047.rectangle,RoutedCases.Batch0852.certificate17049.rectangle,RoutedCases.Batch0852.certificate17051.rectangle,RoutedCases.Batch0852.certificate17053.rectangle,RoutedCases.Batch0852.certificate17059.rectangle,RoutedCases.Batch0853.certificate17061.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17043,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17045,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17047,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17049,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17051,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17053,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17059,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17061,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(59/2000),(119/4000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0852.certificate17041.rectangle,RoutedCases.Batch0852.certificate17042.rectangle,RoutedCases.Batch0852.certificate17043.rectangle,RoutedCases.Batch0852.certificate17044.rectangle,RoutedCases.Batch0852.certificate17046.rectangle,RoutedCases.Batch0852.certificate17048.rectangle,RoutedCases.Batch0852.certificate17050.rectangle,RoutedCases.Batch0852.certificate17054.rectangle,RoutedCases.Batch0852.certificate17056.rectangle,RoutedCases.Batch0853.certificate17062.rectangle,RoutedCases.Batch0853.certificate17064.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17043,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17046,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17054,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17056,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17062,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17064,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(119/4000),(239/8000),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0852.certificate17041.rectangle,RoutedCases.Batch0852.certificate17042.rectangle,RoutedCases.Batch0852.certificate17043.rectangle,RoutedCases.Batch0852.certificate17044.rectangle,RoutedCases.Batch0852.certificate17046.rectangle,RoutedCases.Batch0852.certificate17048.rectangle,RoutedCases.Batch0852.certificate17050.rectangle,RoutedCases.Batch0852.certificate17055.rectangle,RoutedCases.Batch0852.certificate17057.rectangle,RoutedCases.Batch0853.certificate17063.rectangle,RoutedCases.Batch0853.certificate17065.rectangle,RoutedCases.Batch0853.certificate17066.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17043,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17046,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17063,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17065,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17066,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(239/8000),(3/100),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0852.certificate17041.rectangle,RoutedCases.Batch0852.certificate17042.rectangle,RoutedCases.Batch0852.certificate17043.rectangle,RoutedCases.Batch0852.certificate17044.rectangle,RoutedCases.Batch0852.certificate17046.rectangle,RoutedCases.Batch0852.certificate17048.rectangle,RoutedCases.Batch0852.certificate17050.rectangle,RoutedCases.Batch0852.certificate17055.rectangle,RoutedCases.Batch0852.certificate17057.rectangle,RoutedCases.Batch0853.certificate17063.rectangle,RoutedCases.Batch0853.certificate17065.rectangle,RoutedCases.Batch0853.certificate17067.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17041,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17042,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17043,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17044,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17046,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17048,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17050,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17055,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0852.sound17057,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17063,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17065,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0853.sound17067,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(29/1000),(3/100),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_nil _⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source364
