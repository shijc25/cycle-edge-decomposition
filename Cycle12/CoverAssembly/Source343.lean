import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0834
import Cycle12.RoutedCases.Batch0835

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source343

def strip0 : RatCoverRectangle := ⟨(13/1000),(53/4000),20,(some 100)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16683.rectangle,RoutedCases.Batch0834.certificate16685.rectangle,RoutedCases.Batch0834.certificate16687.rectangle,RoutedCases.Batch0834.certificate16691.rectangle,RoutedCases.Batch0834.certificate16696.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16683,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16685,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16687,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16691,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16696,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(53/4000),(27/2000),20,(some 100)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16683.rectangle,RoutedCases.Batch0834.certificate16685.rectangle,RoutedCases.Batch0834.certificate16687.rectangle,RoutedCases.Batch0834.certificate16691.rectangle,RoutedCases.Batch0834.certificate16697.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16683,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16685,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16687,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16691,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16697,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(27/2000),(109/8000),20,(some 100)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16684.rectangle,RoutedCases.Batch0834.certificate16686.rectangle,RoutedCases.Batch0834.certificate16688.rectangle,RoutedCases.Batch0834.certificate16689.rectangle,RoutedCases.Batch0834.certificate16692.rectangle,RoutedCases.Batch0834.certificate16694.rectangle,RoutedCases.Batch0834.certificate16698.rectangle,RoutedCases.Batch0835.certificate16703.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16689,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16692,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16694,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16698,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16703,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(109/8000),(11/800),20,(some 100)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16684.rectangle,RoutedCases.Batch0834.certificate16686.rectangle,RoutedCases.Batch0834.certificate16688.rectangle,RoutedCases.Batch0834.certificate16689.rectangle,RoutedCases.Batch0834.certificate16692.rectangle,RoutedCases.Batch0834.certificate16694.rectangle,RoutedCases.Batch0834.certificate16698.rectangle,RoutedCases.Batch0835.certificate16704.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16689,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16692,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16694,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16698,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16704,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip4 : RatCoverRectangle := ⟨(11/800),(111/8000),20,(some 100)⟩
def pieces4 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16684.rectangle,RoutedCases.Batch0834.certificate16686.rectangle,RoutedCases.Batch0834.certificate16688.rectangle,RoutedCases.Batch0834.certificate16690.rectangle,RoutedCases.Batch0834.certificate16693.rectangle,RoutedCases.Batch0834.certificate16695.rectangle,RoutedCases.Batch0834.certificate16699.rectangle,RoutedCases.Batch0835.certificate16701.rectangle,RoutedCases.Batch0835.certificate16705.rectangle,RoutedCases.Batch0835.certificate16706.rectangle]
theorem valid4 : strip4.JoinS pieces4 := by decide +kernel
theorem sound4 : strip4.Sound := rat_cover_join_s_sound strip4 pieces4 valid4 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16690,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16693,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16695,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16699,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16701,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16705,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16706,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip5 : RatCoverRectangle := ⟨(111/8000),(223/16000),20,(some 100)⟩
def pieces5 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16684.rectangle,RoutedCases.Batch0834.certificate16686.rectangle,RoutedCases.Batch0834.certificate16688.rectangle,RoutedCases.Batch0834.certificate16690.rectangle,RoutedCases.Batch0834.certificate16693.rectangle,RoutedCases.Batch0834.certificate16695.rectangle,RoutedCases.Batch0835.certificate16700.rectangle,RoutedCases.Batch0835.certificate16702.rectangle,RoutedCases.Batch0835.certificate16707.rectangle,RoutedCases.Batch0835.certificate16708.rectangle]
theorem valid5 : strip5.JoinS pieces5 := by decide +kernel
theorem sound5 : strip5.Sound := rat_cover_join_s_sound strip5 pieces5 valid5 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16690,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16693,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16695,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16700,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16702,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16707,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16708,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip6 : RatCoverRectangle := ⟨(223/16000),(447/32000),20,(some 100)⟩
def pieces6 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16684.rectangle,RoutedCases.Batch0834.certificate16686.rectangle,RoutedCases.Batch0834.certificate16688.rectangle,RoutedCases.Batch0834.certificate16690.rectangle,RoutedCases.Batch0834.certificate16693.rectangle,RoutedCases.Batch0834.certificate16695.rectangle,RoutedCases.Batch0835.certificate16700.rectangle,RoutedCases.Batch0835.certificate16702.rectangle,RoutedCases.Batch0835.certificate16707.rectangle,RoutedCases.Batch0835.certificate16709.rectangle,RoutedCases.Batch0835.certificate16710.rectangle]
theorem valid6 : strip6.JoinS pieces6 := by decide +kernel
theorem sound6 : strip6.Sound := rat_cover_join_s_sound strip6 pieces6 valid6 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16690,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16693,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16695,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16700,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16702,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16707,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16710,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip7 : RatCoverRectangle := ⟨(447/32000),(7/500),20,(some 100)⟩
def pieces7 : List RatCoverRectangle := [RoutedCases.Batch0834.certificate16681.rectangle,RoutedCases.Batch0834.certificate16682.rectangle,RoutedCases.Batch0834.certificate16684.rectangle,RoutedCases.Batch0834.certificate16686.rectangle,RoutedCases.Batch0834.certificate16688.rectangle,RoutedCases.Batch0834.certificate16690.rectangle,RoutedCases.Batch0834.certificate16693.rectangle,RoutedCases.Batch0834.certificate16695.rectangle,RoutedCases.Batch0835.certificate16700.rectangle,RoutedCases.Batch0835.certificate16702.rectangle,RoutedCases.Batch0835.certificate16707.rectangle,RoutedCases.Batch0835.certificate16709.rectangle,RoutedCases.Batch0835.certificate16711.rectangle]
theorem valid7 : strip7.JoinS pieces7 := by decide +kernel
theorem sound7 : strip7.Sound := rat_cover_join_s_sound strip7 pieces7 valid7 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16681,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16682,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16684,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16686,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16688,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16690,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16693,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0834.sound16695,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16700,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16702,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16707,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16709,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0835.sound16711,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(13/1000),(7/500),20,(some 100)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3,strip4,strip5,strip6,strip7]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_cons.mpr ⟨sound7,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source343
