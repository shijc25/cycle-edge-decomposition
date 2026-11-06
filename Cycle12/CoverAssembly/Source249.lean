import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0715
import Cycle12.RoutedCases.Batch0716

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source249

def strip0 : RatCoverRectangle := ⟨(9/1000),(19/2000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0715.certificate14304.rectangle,RoutedCases.Batch0715.certificate14305.rectangle,RoutedCases.Batch0715.certificate14307.rectangle,RoutedCases.Batch0715.certificate14309.rectangle,RoutedCases.Batch0715.certificate14311.rectangle,RoutedCases.Batch0715.certificate14313.rectangle,RoutedCases.Batch0715.certificate14318.rectangle,RoutedCases.Batch0715.certificate14319.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14305,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14307,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14309,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14311,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14313,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14318,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14319,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(19/2000),(39/4000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0715.certificate14304.rectangle,RoutedCases.Batch0715.certificate14306.rectangle,RoutedCases.Batch0715.certificate14308.rectangle,RoutedCases.Batch0715.certificate14310.rectangle,RoutedCases.Batch0715.certificate14312.rectangle,RoutedCases.Batch0715.certificate14314.rectangle,RoutedCases.Batch0715.certificate14316.rectangle,RoutedCases.Batch0716.certificate14320.rectangle,RoutedCases.Batch0716.certificate14322.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14306,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14314,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14316,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14320,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14322,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(39/4000),(79/8000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0715.certificate14304.rectangle,RoutedCases.Batch0715.certificate14306.rectangle,RoutedCases.Batch0715.certificate14308.rectangle,RoutedCases.Batch0715.certificate14310.rectangle,RoutedCases.Batch0715.certificate14312.rectangle,RoutedCases.Batch0715.certificate14315.rectangle,RoutedCases.Batch0715.certificate14317.rectangle,RoutedCases.Batch0716.certificate14321.rectangle,RoutedCases.Batch0716.certificate14323.rectangle,RoutedCases.Batch0716.certificate14325.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14306,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14315,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14317,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14321,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14323,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14325,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(79/8000),(1/100),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0715.certificate14304.rectangle,RoutedCases.Batch0715.certificate14306.rectangle,RoutedCases.Batch0715.certificate14308.rectangle,RoutedCases.Batch0715.certificate14310.rectangle,RoutedCases.Batch0715.certificate14312.rectangle,RoutedCases.Batch0715.certificate14315.rectangle,RoutedCases.Batch0715.certificate14317.rectangle,RoutedCases.Batch0716.certificate14321.rectangle,RoutedCases.Batch0716.certificate14324.rectangle,RoutedCases.Batch0716.certificate14325.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14304,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14306,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14308,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14310,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14312,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14315,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0715.sound14317,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14321,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14324,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0716.sound14325,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(9/1000),(1/100),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source249
