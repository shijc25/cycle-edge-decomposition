import Cycle12.RationalCoverAssembly
import Cycle12.RoutedCases.Batch0729
import Cycle12.RoutedCases.Batch0730
import Cycle12.RoutedCases.Batch0731

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CoverAssembly.Source260

def strip0 : RatCoverRectangle := ⟨(19/1000),(77/4000),5,(some 20)⟩
def pieces0 : List RatCoverRectangle := [RoutedCases.Batch0729.certificate14598.rectangle,RoutedCases.Batch0729.certificate14599.rectangle,RoutedCases.Batch0730.certificate14600.rectangle,RoutedCases.Batch0730.certificate14601.rectangle,RoutedCases.Batch0730.certificate14602.rectangle,RoutedCases.Batch0730.certificate14603.rectangle,RoutedCases.Batch0730.certificate14605.rectangle,RoutedCases.Batch0730.certificate14607.rectangle,RoutedCases.Batch0730.certificate14608.rectangle,RoutedCases.Batch0730.certificate14613.rectangle,RoutedCases.Batch0730.certificate14615.rectangle]
theorem valid0 : strip0.JoinS pieces0 := by decide +kernel
theorem sound0 : strip0.Sound := rat_cover_join_s_sound strip0 pieces0 valid0 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14598,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14603,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14605,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14613,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14615,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip1 : RatCoverRectangle := ⟨(77/4000),(39/2000),5,(some 20)⟩
def pieces1 : List RatCoverRectangle := [RoutedCases.Batch0729.certificate14598.rectangle,RoutedCases.Batch0729.certificate14599.rectangle,RoutedCases.Batch0730.certificate14600.rectangle,RoutedCases.Batch0730.certificate14601.rectangle,RoutedCases.Batch0730.certificate14602.rectangle,RoutedCases.Batch0730.certificate14603.rectangle,RoutedCases.Batch0730.certificate14605.rectangle,RoutedCases.Batch0730.certificate14607.rectangle,RoutedCases.Batch0730.certificate14608.rectangle,RoutedCases.Batch0730.certificate14614.rectangle,RoutedCases.Batch0730.certificate14616.rectangle]
theorem valid1 : strip1.JoinS pieces1 := by decide +kernel
theorem sound1 : strip1.Sound := rat_cover_join_s_sound strip1 pieces1 valid1 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14598,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14603,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14605,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14607,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14608,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14614,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14616,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip2 : RatCoverRectangle := ⟨(39/2000),(79/4000),5,(some 20)⟩
def pieces2 : List RatCoverRectangle := [RoutedCases.Batch0729.certificate14598.rectangle,RoutedCases.Batch0729.certificate14599.rectangle,RoutedCases.Batch0730.certificate14600.rectangle,RoutedCases.Batch0730.certificate14601.rectangle,RoutedCases.Batch0730.certificate14602.rectangle,RoutedCases.Batch0730.certificate14604.rectangle,RoutedCases.Batch0730.certificate14606.rectangle,RoutedCases.Batch0730.certificate14609.rectangle,RoutedCases.Batch0730.certificate14611.rectangle,RoutedCases.Batch0730.certificate14617.rectangle,RoutedCases.Batch0730.certificate14619.rectangle]
theorem valid2 : strip2.JoinS pieces2 := by decide +kernel
theorem sound2 : strip2.Sound := rat_cover_join_s_sound strip2 pieces2 valid2 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14598,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14604,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14609,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14611,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14617,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14619,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def strip3 : RatCoverRectangle := ⟨(79/4000),(1/50),5,(some 20)⟩
def pieces3 : List RatCoverRectangle := [RoutedCases.Batch0729.certificate14598.rectangle,RoutedCases.Batch0729.certificate14599.rectangle,RoutedCases.Batch0730.certificate14600.rectangle,RoutedCases.Batch0730.certificate14601.rectangle,RoutedCases.Batch0730.certificate14602.rectangle,RoutedCases.Batch0730.certificate14604.rectangle,RoutedCases.Batch0730.certificate14606.rectangle,RoutedCases.Batch0730.certificate14610.rectangle,RoutedCases.Batch0730.certificate14612.rectangle,RoutedCases.Batch0730.certificate14618.rectangle,RoutedCases.Batch0731.certificate14620.rectangle]
theorem valid3 : strip3.JoinS pieces3 := by decide +kernel
theorem sound3 : strip3.Sound := rat_cover_join_s_sound strip3 pieces3 valid3 (by
  exact List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14598,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0729.sound14599,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14600,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14601,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14602,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14604,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14606,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14610,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14612,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0730.sound14618,List.forall_mem_cons.mpr ⟨RoutedCases.Batch0731.sound14620,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

def rectangle : RatCoverRectangle := ⟨(19/1000),(1/50),5,(some 20)⟩
def strips : List RatCoverRectangle := [strip0,strip1,strip2,strip3]
theorem valid : rectangle.JoinX strips := by decide +kernel
theorem sound : rectangle.Sound := rat_cover_join_x_sound rectangle strips valid (by
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_nil _⟩⟩⟩⟩)

end Cycle12.CoverAssembly.Source260
