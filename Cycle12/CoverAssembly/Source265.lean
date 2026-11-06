import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0737
import Cycle12.RoutedCases.Batch0738

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source265

def strip0 : RatCoverRectangle := ⟨(3/125),(97/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0737.certificate14757.rectangle,RoutedCases.Batch0737.certificate14758.rectangle,RoutedCases.Batch0737.certificate14759.rectangle,RoutedCases.Batch0738.certificate14760.rectangle,RoutedCases.Batch0738.certificate14761.rectangle,RoutedCases.Batch0738.certificate14762.rectangle,RoutedCases.Batch0738.certificate14764.rectangle,RoutedCases.Batch0738.certificate14766.rectangle,RoutedCases.Batch0738.certificate14768.rectangle,RoutedCases.Batch0738.certificate14771.rectangle,RoutedCases.Batch0738.certificate14773.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14757,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14758,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14759,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14760,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14761,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14762,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14764,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14766,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14768,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14771,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14773,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(97/4000),(49/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0737.certificate14757.rectangle,RoutedCases.Batch0737.certificate14758.rectangle,RoutedCases.Batch0737.certificate14759.rectangle,RoutedCases.Batch0738.certificate14760.rectangle,RoutedCases.Batch0738.certificate14761.rectangle,RoutedCases.Batch0738.certificate14762.rectangle,RoutedCases.Batch0738.certificate14764.rectangle,RoutedCases.Batch0738.certificate14766.rectangle,RoutedCases.Batch0738.certificate14768.rectangle,RoutedCases.Batch0738.certificate14772.rectangle,RoutedCases.Batch0738.certificate14774.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14757,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14758,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14759,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14760,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14761,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14762,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14764,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14766,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14768,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14772,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14774,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(49/2000),(99/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0737.certificate14757.rectangle,RoutedCases.Batch0737.certificate14758.rectangle,RoutedCases.Batch0737.certificate14759.rectangle,RoutedCases.Batch0738.certificate14760.rectangle,RoutedCases.Batch0738.certificate14761.rectangle,RoutedCases.Batch0738.certificate14763.rectangle,RoutedCases.Batch0738.certificate14765.rectangle,RoutedCases.Batch0738.certificate14767.rectangle,RoutedCases.Batch0738.certificate14769.rectangle,RoutedCases.Batch0738.certificate14770.rectangle,RoutedCases.Batch0738.certificate14775.rectangle,RoutedCases.Batch0738.certificate14777.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14757,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14758,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14759,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14760,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14761,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14763,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14765,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14767,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14769,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14775,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14777,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(99/4000),(1/40),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0737.certificate14757.rectangle,RoutedCases.Batch0737.certificate14758.rectangle,RoutedCases.Batch0737.certificate14759.rectangle,RoutedCases.Batch0738.certificate14760.rectangle,RoutedCases.Batch0738.certificate14761.rectangle,RoutedCases.Batch0738.certificate14763.rectangle,RoutedCases.Batch0738.certificate14765.rectangle,RoutedCases.Batch0738.certificate14767.rectangle,RoutedCases.Batch0738.certificate14769.rectangle,RoutedCases.Batch0738.certificate14770.rectangle,RoutedCases.Batch0738.certificate14776.rectangle,RoutedCases.Batch0738.certificate14778.rectangle,RoutedCases.Batch0738.certificate14779.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14757,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14758,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0737.sound14759,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14760,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14761,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14763,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14765,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14767,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14769,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14770,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14776,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14778,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0738.sound14779,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(3/125),(1/40),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source265
